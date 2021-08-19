{-# LANGUAGE DefaultSignatures #-}

-- | Binding library
module Support.SubstOpt where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as S
import GHC.Generics
import GHC.Stack
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import qualified Util.Lambda as LC

-------------------------------------------------------------------

-- | Type class of syntactic forms that contain variable constructors
class VarC a where
  var :: Var -> a

  isvar :: a -> Maybe Var
  isvar _ = Nothing
  {-# INLINE isvar #-}

class AlphaC a where
  fv :: a -> Set IdInt
  default fv :: (Generic a, GAlpha (Rep a)) => a -> Set IdInt
  fv x = gfv (from x)
  {-# INLINE fv #-}

  bv :: a -> Set Int

  -- | replace bound variables (starting at k) with a list of free variables (i.e. [IdInt])
  -- NOTE: the term may not be locally closed, so what do we do in that case???
  multi_open_rec :: HasCallStack => Int -> [Var] -> a -> a

  -- | replace free variables (noted as "IdInt") with their respective bound variables
  multi_close_rec :: HasCallStack => Int -> [IdInt] -> a -> a
  default multi_close_rec :: (Generic a, GAlpha (Rep a)) => Int -> [IdInt] -> a -> a
  multi_close_rec k vs x = to (gmulti_close_rec k vs (from x))
  {-# INLINE multi_close_rec #-}

class AlphaC a => SubstC b a where
  -- | substitute for a single free variable
  -- substFv :: b -> IdInt -> a -> a

  -- | substitute for multiple bound variables (starting at index 0)
  multi_subst_bv :: HasCallStack => [b] -> a -> a
  default multi_subst_bv :: (Generic a, VarC b, GOpen b (Rep a), a ~ b, HasCallStack) => [b] -> a -> a
  multi_subst_bv vs x =
    case isvar x of
      Just v -> substBvVar vs v
      Nothing -> to (gmulti_subst_bv vs (from x))
  {-# INLINE multi_subst_bv #-}

--------------------------------------------------------------

-- | Variables, bound and free
data Var = B Int | F IdInt deriving (Generic, Eq, Show)

instance NFData Var

--instance VarC Var where
--  var = id
--  isvar x = Just x

instance AlphaC Var where
  fv (B _) = S.empty
  fv (F x) = S.singleton x
  {-# INLINE fv #-}

  bv (B i) = S.singleton i
  bv (F _) = S.empty

  multi_close_rec k xs (F x) =
    case elemIndex x xs of
      Just n -> B (n + k)
      Nothing -> F x
  multi_close_rec _k _xs (B n2) = (B n2)
  {-# INLINE multi_close_rec #-}

  multi_open_rec = substBvVarVar
  {-# INLINE multi_open_rec #-}

-- We need this instance for the generic version
-- but we should *never* use it
-- NB: may make sense to include overlapping instances
-- b/c the SubstC Var Var instance does work.
instance SubstC b Var where
  multi_subst_bv _ = error "BUG: should not reach here"
  {-# INLINE multi_subst_bv #-}

substBvVarVar :: HasCallStack => Int -> [Var] -> Var -> Var
substBvVarVar _k _ (F x) = (F x)
substBvVarVar k vs (B i)
  | i >= k && i - k < length vs = vs !! (i - k)
  | otherwise = B i
{-# INLINEABLE substBvVarVar #-}

substBvVar :: HasCallStack => VarC a => [a] -> Var -> a
substBvVar _ (F x) = var (F x)
substBvVar vs (B i) = vs !! i
{-# INLINEABLE substBvVar #-}

substFvVar :: HasCallStack => VarC a => a -> IdInt -> Var -> a
substFvVar _ _ (B n) = var (B n)
substFvVar u y (F x) = if x == y then u else (var (F x))
{-# INLINEABLE substFvVar #-}

-------------------------------------------------------------------

-- Caching open/close at binders.
-- To speed up this implementation, we delay the execution of subst_bv / open / close
-- in a binder so that multiple traversals can fuse together

data Bind a where
  Bind :: !a -> Bind a
  BindSubst :: ![a] -> !a -> Bind a
  BindOpen :: Int -> ![Var] -> !a -> Bind a
  BindClose :: !Int -> ![IdInt] -> !a -> Bind a
  deriving (Generic, Show)

instance (NFData a) => NFData (Bind a)

instance (Eq a, SubstC a a, Show a) => Eq (Bind a) where
  b1 == b2 = unbind b1 == unbind b2

-- create a binding by "abstracting a variable"
bind :: a -> Bind a
bind = Bind
{-# INLINEABLE bind #-}

unbind :: (SubstC a a, HasCallStack, Show a) => Bind a -> a
unbind b =
  go b
  where
    go (Bind a) = a
    go (BindSubst ss a) = multi_subst_bv ss a
    go (BindOpen k ss a) = multi_open_rec (k + 1) ss a
    go (BindClose k vs a) = multi_close_rec k vs a
{-# INLINEABLE unbind #-}

instance (SubstC a a, Show a) => AlphaC (Bind a) where
  {-# SPECIALIZE instance (SubstC a a, Show a) => AlphaC (Bind a) #-}
  fv :: Bind a -> Set IdInt
  fv b = fv (unbind b)
  {-# INLINE fv #-}

  bv :: Bind a -> Set Int
  bv b = S.filter (\x -> x >= 0) $ S.map (\x -> x - 1) (bv (unbind b))

  multi_open_rec k vn (BindOpen l vm b) = BindOpen l (vm <> vn) b
  multi_open_rec k vn (Bind b) = BindOpen k vn b
  multi_open_rec k vn b = BindOpen k vn (unbind b)
  {-# INLINE multi_open_rec #-}

  multi_close_rec k xs b = case b of
    (BindClose k0 ys a) -> (BindClose k0 (ys <> xs) a)
    _ -> (BindClose (k + 1) xs (unbind b))
  {-# INLINE multi_close_rec #-}

instance (SubstC a a, Show a) => SubstC a (Bind a) where
  {-# SPECIALIZE instance (SubstC a a, Show a) => SubstC a (Bind a) #-}
  multi_subst_bv vn (BindSubst vm b) = BindSubst (vm <> vn) b
  multi_subst_bv vn b = BindSubst vn (unbind b)
  {-# INLINE multi_subst_bv #-}

-- | Note: the binding should be localy closed
instantiate :: (SubstC a a, Show a) => Bind a -> a -> a
instantiate (BindSubst vs e) u = multi_subst_bv (u : vs) e
instantiate b u = multi_subst_bv [u] (unbind b)
{-# INLINEABLE instantiate #-}

-----------------------------------------------------------------

open :: HasCallStack => SubstC a a => Show a => Bind a -> Var -> a
open b x =
  --trace ("open c:" ++ show b ++ " with " ++ show x) $
  let b' = case b of
        (BindOpen k vs e) -> multi_open_rec k (x : vs) e
        _ -> multi_open_rec 0 [x] (unbind b)
   in -- trace ("open r: " ++ show b') $
      b'
{-# INLINEABLE open #-}

close :: Show a => IdInt -> a -> Bind a
close x e = BindClose 0 [x] e
{-# INLINEABLE close #-}

---------------------------------------------------------------------

class GAlpha f where
  gfv :: f a -> Set IdInt
  gmulti_close_rec :: Int -> [IdInt] -> f a -> f a

class GOpen b f where
  gmulti_subst_bv :: [b] -> f a -> f a

-------------------------------------------------------------------

-- Constant types
instance (SubstC b c) => GOpen b (K1 i c) where
  gmulti_subst_bv vs (K1 c) = K1 (multi_subst_bv vs c)
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b U1 where
  gmulti_subst_bv _v U1 = U1
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b f => GOpen b (M1 i c f) where
  gmulti_subst_bv vs = M1 . gmulti_subst_bv vs . unM1
  {-# INLINE gmulti_subst_bv #-}

instance GOpen b V1 where
  gmulti_subst_bv _vs = id
  {-# INLINE gmulti_subst_bv #-}

instance (GOpen b f, GOpen b g) => GOpen b (f :*: g) where
  gmulti_subst_bv vs (f :*: g) = gmulti_subst_bv vs f :*: gmulti_subst_bv vs g
  {-# INLINE gmulti_subst_bv #-}

instance (GOpen b f, GOpen b g) => GOpen b (f :+: g) where
  gmulti_subst_bv vs (L1 f) = L1 $ gmulti_subst_bv vs f
  gmulti_subst_bv vs (R1 g) = R1 $ gmulti_subst_bv vs g
  {-# INLINE gmulti_subst_bv #-}

instance SubstC b Int where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Bool where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b () where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Char where
  multi_subst_bv _ = id
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GOpen b (Rep [a])) => SubstC b [a] where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GOpen b (Rep (Maybe a))) => SubstC b (Maybe a) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (Either a1 a2), AlphaC (Either a1 a2), GOpen b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (a, b), AlphaC (a, b), GOpen c (Rep (a, b))) => SubstC c (a, b) where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance
  ( Generic (a, b, d),
    AlphaC (a, b, d),
    GOpen c (Rep (a, b, d))
  ) =>
  SubstC c (a, b, d)
  where
  multi_subst_bv xs x = to $ gmulti_subst_bv xs (from x)
  {-# INLINE multi_subst_bv #-}

----------------------------------------------------------------

instance (AlphaC c) => GAlpha (K1 i c) where
  gfv (K1 c) = (fv c)
  gmulti_close_rec x xs (K1 c) = K1 (multi_close_rec x xs c)
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha U1 where
  gfv U1 = S.empty
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha f => GAlpha (M1 i c f) where
  gfv = gfv . unM1
  gmulti_close_rec x xs = M1 . gmulti_close_rec x xs . unM1
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha V1 where
  gfv _s = S.empty
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gfv (f :*: g) = gfv f `S.union` gfv g
  gmulti_close_rec x xs (f :*: g) =
    gmulti_close_rec x xs f :*: gmulti_close_rec x xs g
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gfv (L1 f) = gfv f
  gfv (R1 g) = gfv g
  gmulti_close_rec x xs (L1 f) = L1 $ gmulti_close_rec x xs f
  gmulti_close_rec x xs (R1 g) = R1 $ gmulti_close_rec x xs g
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance AlphaC Int where
  fv _ = S.empty
  multi_open_rec _ _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC Bool where
  fv _ = S.empty
  multi_open_rec _ _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC () where
  fv _ = S.empty
  multi_open_rec _ _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC Char where
  fv _ = S.empty
  multi_open_rec _ _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC String where
  fv _ = S.empty
  multi_open_rec _ _ = id
  multi_close_rec _ _ = id
  {-# INLINE fv #-}
  {-# INLINE multi_close_rec #-}

instance AlphaC a => AlphaC [a] where
  multi_open_rec k ss = map (multi_open_rec k ss)

instance AlphaC a => AlphaC (Maybe a) where
  multi_open_rec k ss = fmap (multi_open_rec k ss)

-- instance (AlphaC a1, AlphaC a2) => AlphaC (Either a1 a2)

-- instance (AlphaC a, AlphaC b) => AlphaC (a, b)

-- instance (AlphaC a, AlphaC b, AlphaC d) => AlphaC (a, b, d)
