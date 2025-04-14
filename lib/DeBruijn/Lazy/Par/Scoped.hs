{-# LANGUAGE StandaloneDeriving #-}

-- | Well-scoped de Bruijn indices + parallel (explicit) substitutions
-- hidden in library (see Support.Par.SubstScoped)
module DeBruijn.Lazy.Par.Scoped (toDB, impl) where

import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Support.Par.SubstScoped
import Text.PrettyPrint.HughesPJ
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Nat (Idx (..), Nat (..), toInt)
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Lazy.Par.Scoped",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

-- NOTE: making the Idx strict, significantly degrades performance, hmmm....
data DB n where
  DVar :: (Idx n) -> DB n
  DLam :: (Bind DB n) -> DB n
  DApp :: (DB n) -> (DB n) -> DB n
  DBool :: Bool -> DB n
  DIf :: DB n -> DB n -> DB n -> DB n

-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (DB n)

instance NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c


----------------------------------------------------------
-- uses the SubstScoped library
instance SubstC DB where
  var = DVar
  {-# INLINEABLE var #-}

  subst s (DVar i) = applyS s i
  subst s (DLam b) = DLam (substBind s b)
  subst s (DApp f a) = DApp (subst s f) (subst s a)
  subst s (DBool b) = DBool b
  subst s (DIf a b c) = DIf (subst s a) (subst s b) (subst s c)
  {-# INLINEABLE subst #-}

{-# SPECIALIZE applyS :: Sub DB n m -> Idx n -> DB m #-}

{-# SPECIALIZE nil :: Sub DB n n #-}

{-# SPECIALIZE comp :: Sub DB m n -> Sub DB n p -> Sub DB m p #-}

{-# SPECIALIZE lift :: Sub DB n m -> Sub DB ('S n) ('S m) #-}

{- SPECIALIZE single :: DB n -> Sub DB ('S n) n -}
{-# SPECIALIZE unbind :: Bind DB n -> DB ('S n) #-}

{-# SPECIALIZE instantiate :: Bind DB n -> DB n -> DB n #-}

{-# SPECIALIZE substBind :: Sub DB n m -> Bind DB n -> Bind DB m #-}

----------------------------------------------------------

-- Computing the normal form proceeds as usual.

nf :: DB n -> DB n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a') (nf b) (nf c)

whnf :: DB n -> DB n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c

---------------------------------------------------------------

nfi :: Int -> DB n -> Stats.M (DB n)
nfi 0 _ = Stats.done
nfi _ e@(DVar _) = return e
nfi n (DLam b) = DLam . bind <$> nfi (n - 1) (unbind b)
nfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    DLam b -> Stats.count >> nfi (n - 1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB n -> Stats.M (DB n)
whnfi 0 _ = Stats.done
whnfi _ e@(DVar _) = return e
whnfi _ e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ DApp f' a

---------------------------------------------------------
{-
Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. NOTE: input term
must be closed or 'fromJust' will error.
-}

toDB :: LC IdInt -> DB 'Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC IdInt -> DB n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam (bind b')
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b)  = DBool b
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)

-- Convert back from deBruijn to the LC type.

fromDB :: DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b) (from n c)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (DB n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text ("\\.") PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
