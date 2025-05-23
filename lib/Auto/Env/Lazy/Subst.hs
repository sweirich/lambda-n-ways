{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Well-scoped de Bruijn indices (lazy)
-- with naive substitution, using substitution from 
module Auto.Env.Lazy.Subst (toDB, impl) where

import Rebound
import Data.Fin
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
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
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Env.Lazy.Subst",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==), 
      impl_eval = eval
    }

data DB n where
  DVar :: Fin n -> DB n
  DLam :: DB (S n) -> DB n
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
instance SubstVar DB where
  var = DVar
  {-# INLINEABLE var #-}

instance Subst DB DB where
  applyE s (DVar i) = applyEnv s i
  applyE s (DLam b) = DLam (applyE (up s) b)
  applyE s (DApp f a) = DApp (applyE s f) (applyE s a)
  applyE s (DIf a b c) = DIf (applyE s a) (applyE s b) (applyE s c)
  applyE s (DBool b) = DBool b
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE applyEnv :: Env DB n m -> Fin n -> DB m #-}

{-# SPECIALIZE idE :: Env DB n n #-}

{-# SPECIALIZE (.>>) :: Env DB m n -> Env DB n p -> Env DB m p #-}


{-# SPECIALIZE up :: Env DB n m -> Env DB ('S n) ('S m) #-}


----------------------------------------------------------

-- Computing the normal form proceeds as usual.

nf :: DB n -> DB n
nf e@(DVar _) = e
nf (DLam b) = DLam (nf b)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (applyE (a .: idE) b)
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a) (nf b) (nf c)

whnf :: DB n -> DB n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (applyE (a .: idE) b)
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c



eval :: DB n -> DB n
eval e@(DVar _) = e
eval e@(DLam _) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (applyE (a .: idE) b)
    f' -> f' 
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval b
    DBool False -> eval c
    a' -> DIf a' b c

---------------------------------------------------------
{-
Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. NOTE: input term
must be closed or 'fromJust' will error.
-}

toDB :: LC IdInt -> DB 'Z
toDB = to []
  where
    to :: [(IdInt, Fin n)] -> LC IdInt -> DB n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam b'
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
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n)  b)
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
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 b
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
