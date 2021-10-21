{-# LANGUAGE DefaultSignatures #-}

-- | Binding library for locally nameless representation
module Support.SubstOptRefactor
  ( VarC (..),
    AlphaC (..),
    SubstC (..),
    Var (..),
    isBound,
    isFree,
    prettyVar,
    multiSubstBvVar,
    multiSubstFvVar,
    substFvVar,
    substBvVar,
    Bind,
    bind,
    unbind,
    instantiate,
    open,
    close,
    substFv,
    GAlpha (..),
    GSubst (..),
  )
where

import qualified Control.Monad.State as State
import Data.List (elemIndex)
import Debug.Trace
import GHC.Generics
import GHC.Stack
import Util.IdInt (IdInt (..), firstBoundId)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import qualified Util.Syntax.Lambda as LC

-------------------------------------------------------------------

-- | Type class of syntactic forms that contain variable constructors
class VarC a where
  var :: Var -> a

  isvar :: a -> Maybe Var
  isvar _ = Nothing
  {-# INLINE isvar #-}

-- | Type for syntactic forms
class AlphaC a where
  -- | calculate the free variables of a term
  fv :: a -> S.IdIntSet
  default fv :: (Generic a, GAlpha (Rep a)) => a -> S.IdIntSet
  fv x = gfv (from x)
  {-# INLINE fv #-}

  -- | replace bound variables (starting at k) with a list of free variables (i.e. [IdInt])
  -- NOTE: the term we are replacing into may not be locally closed
  multi_open_rec :: Int -> [Var] -> a -> a
  default multi_open_rec :: (Generic a, GAlpha (Rep a)) => Int -> [Var] -> a -> a
  multi_open_rec k vs x = to (gmulti_open_rec k vs (from x))

  -- | replace free variables (noted as "IdInt") with their respective bound variables
  -- starting at index k
  multi_close_rec :: Int -> [IdInt] -> a -> a
  default multi_close_rec :: (Generic a, GAlpha (Rep a)) => Int -> [IdInt] -> a -> a
  multi_close_rec k vs x = to (gmulti_close_rec k vs (from x))
  {-# INLINE multi_close_rec #-}

-- | Type class for substitution functions
class AlphaC a => SubstC b a where
  -- | substitute for multiple free variables
  multi_subst_fv :: M.IdIntMap b -> a -> a
  default multi_subst_fv :: (Generic a, VarC b, GSubst b (Rep a), a ~ b) => M.IdIntMap b -> a -> a
  multi_subst_fv vs x =
    case isvar x of
      Just v -> multiSubstFvVar vs v
      Nothing -> to (gmulti_subst_fv vs (from x))

  -- | substitute for multiple bound variables (starting at index k)
  multi_subst_bv :: Int -> [b] -> a -> a
  default multi_subst_bv :: (Generic a, VarC b, GSubst b (Rep a), a ~ b) => Int -> [b] -> a -> a
  multi_subst_bv k vs x =
    case isvar x of
      Just v -> multiSubstBvVar k vs v
      Nothing -> to (gmulti_subst_bv k vs (from x))
  {-# INLINE multi_subst_bv #-}

--------------------------------------------------------------

-- | Variables, bound and free
data Var = B Int | F IdInt deriving (Generic, Eq, Show)

isBound :: Var -> Bool
isBound (B _) = True
isBound (F _) = False

isFree :: Var -> Bool
isFree (B _) = False
isFree (F _) = True

-- | Display the variable without the outermost constructor
prettyVar :: Var -> String
prettyVar (B i) = "b" ++ show i
prettyVar (F x) = show x

instance NFData Var

instance VarC Var where
  var = id
  isvar x = Just x

instance AlphaC Var where
  fv (B _) = S.empty
  fv (F x) = S.singleton x
  {-# INLINE fv #-}

  --bv (B i) = S.singleton i
  --bv (F _) = S.empty

  multi_close_rec k xs (F x) =
    case elemIndex x xs of
      Just n -> B (n + k)
      Nothing -> F x
  multi_close_rec _k _xs (B n2) = (B n2)
  {-# INLINE multi_close_rec #-}

  multi_open_rec _k _ (F x) = F x
  multi_open_rec k vs v@(B i) = nthWithDefault (var v) vs (i - k)
  --    | i >= k && i - k < length vs = vs !! (i - k)
  --    | otherwise = B i
  {-# INLINE multi_open_rec #-}

-- We need this instance for the generic version
-- but we should *never* use it
-- NB: may make sense to include overlapping instances?
-- b/c the SubstC Var Var instance does make sense.
instance SubstC b Var where
  multi_subst_fv _ _ = error "BUG: should not reach here"
  multi_subst_bv _k _ = error "BUG: should not reach here"
  {-# INLINE multi_subst_bv #-}

nthWithDefault :: forall a. a -> [a] -> Int -> a
nthWithDefault a xs i
  | i < 0 = a
  | otherwise = go i xs
  where
    go :: Int -> [a] -> a
    go 0 (x : _) = x
    go j (_ : ys) = go (j - 1) ys
    go _ [] = a
{-# INLINE nthWithDefault #-}

-- | multi substitution for a single bound variable
-- starts at index k leaves all other variables alone
multiSubstBvVar :: (VarC a) => Int -> [a] -> Var -> a
multiSubstBvVar k vs v@(B i) =
  -- trace ("nth for " ++ show i ++ " - " ++ show k) $
  nthWithDefault (var v) vs (i - k)
multiSubstBvVar _ _ v = var v
{-# INLINEABLE multiSubstBvVar #-}

-- | multi substitution for a single free variable
multiSubstFvVar :: VarC a => M.IdIntMap a -> Var -> a
multiSubstFvVar m v@(F x) = M.findWithDefault (var v) x m
multiSubstFvVar _ v@(B _) = var v

-- | single substitution for a single bound variable (0)
substBvVar :: (VarC a) => a -> Var -> a
substBvVar u = multiSubstBvVar 0 [u]

-- | single substitution for a single free variable
substFvVar :: VarC a => a -> IdInt -> Var -> a
substFvVar u y (F x) | x == y = u
substFvVar _ _ v = var v
{-# INLINEABLE substFvVar #-}

-------------------------------------------------------------------

-- Caching open/close at binders.
-- To speed up this implementation, we delay the execution of subst_bv / open / close
-- in a binder so that multiple traversals can fuse together

data Bind a where
  Bind :: [BindInfo a] -> !a -> Bind a
  deriving (Generic, Show)

data BindInfo a where
  SubstBv :: !Int -> ![a] -> BindInfo a
  SubstFv :: !(M.IdIntMap a) -> BindInfo a
  Open :: !Int -> ![Var] -> BindInfo a
  Close :: !Int -> ![IdInt] -> BindInfo a
  deriving (Generic, Show)

instance (NFData a) => NFData (BindInfo a)

instance (NFData a) => NFData (Bind a)

instance (Eq a, SubstC a a, Show a) => Eq (Bind a) where
  b1 == b2 = unbind b1 == unbind b2

-- | create a binding by "abstracting a variable"
bind :: AlphaC a => a -> Bind a
bind a = Bind [] a
{-# INLINEABLE bind #-}

addBindInfo :: (Show a, SubstC a a) => BindInfo a -> Bind a -> Bind a
addBindInfo bi (Bind bis0 a) = Bind (add bi bis0) a
  where
    {-    add x@(Open k vn) y@(Open l vm : bis)
          | l - k == length vn =
                 trace (" Open^ k=" ++ show k ++ " vn=" ++ show vn ++ " l=" ++ show l ++ " vm=" ++ show vm) $
                   add (Open l (vn <> vm)) bis -}
    add (Close _k xs) (Close k0 ys : bis) =
      add (Close k0 (ys <> xs)) bis
    add (SubstBv k vn) (SubstBv l vm : bis)
      | l - k == length vn =
        add (SubstBv k (vn <> vm)) bis
      | otherwise =
        trace ("VIOLATION k=" ++ show k ++ " |vn|=" ++ show (length vn) ++ " l=" ++ show l) $
          add (SubstBv k (vn <> vm)) bis
    -- add (SubstFv m1) (SubstFv m2 : bis) = trace "subst" $ add (SubstFv (m1 `comp` m2)) bis
    add (SubstFv m1) (Open k vm : bis)
      | fm `isDom` m1 = add (SubstBv k (map (m1 M.!) fm)) bis
      where
        fm = freeVars vm
    add x bis = (x : bis)
{-# INLINEABLE addBindInfo #-}

unbind :: (SubstC a a, Show a) => Bind a -> a
unbind b@(Bind bis a) =
  -- ("unbind c: " ++ show b) $
  -- ("unbind r: " ++ show result) $
  result
  where
    result = applyAll bis a
{-# INLINEABLE unbind #-}

apply :: SubstC a a => BindInfo a -> a -> a
apply (SubstBv k ss) = multi_subst_bv k ss
apply (SubstFv m) = multi_subst_fv m
apply (Open k ss) = multi_open_rec k ss
apply (Close k vs) = multi_close_rec k vs

-- Compress and apply the delayed operations in the body of the term
applyAll :: (Show a, SubstC a a) => [BindInfo a] -> a -> a
applyAll [] = id
applyAll (bi : bis) = apply bi . applyAll bis

freeVars :: [Var] -> [IdInt]
freeVars [] = []
freeVars (F x : xs) = x : freeVars xs
freeVars (B _ : xs) = freeVars xs

instance (SubstC a a, Show a) => AlphaC (Bind a) where
  {-# SPECIALIZE instance (SubstC a a, Show a) => AlphaC (Bind a) #-}
  fv :: Bind a -> S.IdIntSet
  fv b = fv (unbind b)
  {-# INLINE fv #-}

  multi_open_rec k vn b =
    -- Bind [] $ unbind
    (addBindInfo (Open (k + 1) vn) b)
  {-# INLINE multi_open_rec #-}

  multi_close_rec k xs = addBindInfo (Close (k + 1) xs)
  {-# INLINE multi_close_rec #-}

instance (SubstC a a, Show a) => SubstC a (Bind a) where
  {-# SPECIALIZE instance (SubstC a a, Show a) => SubstC a (Bind a) #-}
  multi_subst_bv k vn = (addBindInfo (SubstBv (k + 1) vn))
  {-# INLINE multi_subst_bv #-}

  multi_subst_fv m1 b =
    -- Bind [] $ unbind
    (addBindInfo (SubstFv m1) b)
  {-# INLINE multi_subst_fv #-}

isDom :: [IdInt] -> M.IdIntMap a -> Bool
isDom fm m = S.fromList fm == M.keysSet m

-- | Note: in this case, the binding should be locally closed
instantiate :: (SubstC a a, Show a) => Bind a -> a -> a
instantiate b u = result
  where
    result = unbind (addBindInfo (SubstBv 0 [u]) b)
{-# INLINEABLE instantiate #-}

substSub :: (Functor f, SubstC b a) => M.IdIntMap b -> f a -> f a
substSub s2 s1 = fmap (multi_subst_fv s2) s1
{-# INLINEABLE substSub #-}

comp :: SubstC a a => M.IdIntMap a -> M.IdIntMap a -> M.IdIntMap a
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = substSub s1 s2 <> s1
{-# INLINEABLE comp #-}

-----------------------------------------------------------------

open :: SubstC a a => Show a => Bind a -> Var -> a
open b x = unbind (addBindInfo (Open 0 [x]) b)
{-# INLINEABLE open #-}

close :: (AlphaC a, Show a) => IdInt -> a -> Bind a
close x e = Bind [Close 0 [x]] e
{-# INLINEABLE close #-}

substFv :: (Show a, SubstC b a) => b -> IdInt -> a -> a
substFv b x a =
  --trace ("subst c: " ++ show a) $
  -- trace ("subst r: " ++ show result) $
  result
  where
    result = multi_subst_fv (M.singleton x b) a
{-# INLINEABLE substFv #-}

---------------------------------------------------------------------

class GAlpha f where
  gfv :: f a -> S.IdIntSet
  gmulti_open_rec :: Int -> [Var] -> f a -> f a
  gmulti_close_rec :: Int -> [IdInt] -> f a -> f a

class GSubst b f where
  gmulti_subst_bv :: Int -> [b] -> f a -> f a
  gmulti_subst_fv :: M.IdIntMap b -> f a -> f a

-- | Generic instances for substitution
instance (SubstC b c) => GSubst b (K1 i c) where
  gmulti_subst_bv k vs (K1 c) = K1 (multi_subst_bv k vs c)
  gmulti_subst_fv m (K1 c) = K1 (multi_subst_fv m c)
  {-# INLINE gmulti_subst_bv #-}

instance GSubst b U1 where
  gmulti_subst_bv _k _v U1 = U1
  gmulti_subst_fv _m U1 = U1
  {-# INLINE gmulti_subst_bv #-}

instance GSubst b f => GSubst b (M1 i c f) where
  gmulti_subst_bv k vs = M1 . gmulti_subst_bv k vs . unM1
  gmulti_subst_fv vs = M1 . gmulti_subst_fv vs . unM1
  {-# INLINE gmulti_subst_bv #-}

instance GSubst b V1 where
  gmulti_subst_bv _k _vs = id
  gmulti_subst_fv _vs = id
  {-# INLINE gmulti_subst_bv #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gmulti_subst_bv k vs (f :*: g) = gmulti_subst_bv k vs f :*: gmulti_subst_bv k vs g
  gmulti_subst_fv vs (f :*: g) = gmulti_subst_fv vs f :*: gmulti_subst_fv vs g
  {-# INLINE gmulti_subst_bv #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gmulti_subst_bv k vs (L1 f) = L1 $ gmulti_subst_bv k vs f
  gmulti_subst_bv k vs (R1 g) = R1 $ gmulti_subst_bv k vs g
  gmulti_subst_fv vs (L1 f) = L1 $ gmulti_subst_fv vs f
  gmulti_subst_fv vs (R1 g) = R1 $ gmulti_subst_fv vs g
  {-# INLINE gmulti_subst_bv #-}

instance SubstC b Int where
  multi_subst_bv _k _ = id
  multi_subst_fv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Bool where
  multi_subst_bv _k _ = id
  multi_subst_fv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b () where
  multi_subst_bv _k _ = id
  multi_subst_fv _ = id
  {-# INLINE multi_subst_bv #-}

instance SubstC b Char where
  multi_subst_bv _k _ = id
  multi_subst_fv _ = id
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GSubst b (Rep [a])) => SubstC b [a] where
  multi_subst_bv k xs x = to $ gmulti_subst_bv k xs (from x)
  multi_subst_fv m x = to $ gmulti_subst_fv m (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic a, AlphaC a, GSubst b (Rep (Maybe a))) => SubstC b (Maybe a) where
  multi_subst_bv k xs x = to $ gmulti_subst_bv k xs (from x)
  multi_subst_fv xs x = to $ gmulti_subst_fv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (Either a1 a2), AlphaC (Either a1 a2), GSubst b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  multi_subst_bv k xs x = to $ gmulti_subst_bv k xs (from x)
  multi_subst_fv xs x = to $ gmulti_subst_fv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance (Generic (a, b), AlphaC (a, b), GSubst c (Rep (a, b))) => SubstC c (a, b) where
  multi_subst_bv k xs x = to $ gmulti_subst_bv k xs (from x)
  multi_subst_fv xs x = to $ gmulti_subst_fv xs (from x)
  {-# INLINE multi_subst_bv #-}

instance
  ( Generic (a, b, d),
    AlphaC (a, b, d),
    GSubst c (Rep (a, b, d))
  ) =>
  SubstC c (a, b, d)
  where
  multi_subst_bv k xs x = to $ gmulti_subst_bv k xs (from x)
  multi_subst_fv xs x = to $ gmulti_subst_fv xs (from x)
  {-# INLINE multi_subst_bv #-}

----------------------------------------------------------------
-- Generic instances for Alpha

instance (AlphaC c) => GAlpha (K1 i c) where
  gfv (K1 c) = (fv c)
  gmulti_open_rec x xs (K1 c) = K1 (multi_open_rec x xs c)
  gmulti_close_rec x xs (K1 c) = K1 (multi_close_rec x xs c)
  {-# INLINE gfv #-}
  {-# INLINE gmulti_open_rec #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha U1 where
  gfv U1 = S.empty
  gmulti_open_rec _ _ = id
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha f => GAlpha (M1 i c f) where
  gfv = gfv . unM1
  gmulti_open_rec x xs = M1 . gmulti_open_rec x xs . unM1
  gmulti_close_rec x xs = M1 . gmulti_close_rec x xs . unM1
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance GAlpha V1 where
  gfv _s = S.empty
  gmulti_open_rec _ _ = id
  gmulti_close_rec _ _ = id
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gfv (f :*: g) = gfv f `S.union` gfv g
  gmulti_open_rec x xs (f :*: g) =
    gmulti_open_rec x xs f :*: gmulti_open_rec x xs g
  gmulti_close_rec x xs (f :*: g) =
    gmulti_close_rec x xs f :*: gmulti_close_rec x xs g
  {-# INLINE gfv #-}
  {-# INLINE gmulti_close_rec #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gfv (L1 f) = gfv f
  gfv (R1 g) = gfv g
  gmulti_open_rec x xs (L1 f) = L1 $ gmulti_open_rec x xs f
  gmulti_open_rec x xs (R1 g) = R1 $ gmulti_open_rec x xs g
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

instance AlphaC a => AlphaC [a]

instance AlphaC a => AlphaC (Maybe a)

instance (AlphaC a1, AlphaC a2) => AlphaC (Either a1 a2)

instance (AlphaC a, AlphaC b) => AlphaC (a, b)

instance (AlphaC a, AlphaC b, AlphaC d) => AlphaC (a, b, d)
