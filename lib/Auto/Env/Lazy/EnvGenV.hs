{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- Use the Rebound library, with a lazy datatype
-- generic programming for implementation
-- environment argument for whnf function
-- evaluate argument before adding to environment
module Auto.Env.Lazy.EnvGenV (toDB, impl) where

import Rebound
import Rebound.Bind.Single
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
import GHC.Generics hiding (S)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Env.Lazy.EnvGenV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_eval = whnf idE,
      impl_aeq = (==)
    }

data DB n where
  DVar :: (Fin n) -> DB n
  DLam :: (Bind DB DB n) -> DB n
  DApp :: (DB n) -> (DB n) -> DB n
  DBool :: Bool -> DB n
  DIf :: DB n -> DB n -> DB n -> DB n

deriving instance Generic1 DB
-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (DB n)

instance Eq (Bind DB DB n) where
  b1 == b2 = getBody b1 == getBody b2

instance NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

instance (Subst v e, Subst v v, forall n. NFData (e n)) => NFData (Bind v e n) where
  rnf b = rnf (getBody b)

----------------------------------------------------------

instance SubstVar DB where
  var = DVar
  {-# INLINEABLE var #-}

instance Subst DB DB where
  applyE r (DVar x) = applyEnv r x
  applyE r e = gapplyE r e
  -- generic

{-# SPECIALIZE idE :: Env DB n n #-}

{-# SPECIALIZE (.>>) :: Env DB m n -> Env DB n p -> Env DB m p #-}

{-# SPECIALIZE up :: Env DB n m -> Env DB ('S n) ('S m) #-}

{-# SPECIALIZE getBody :: Bind DB DB n -> DB ('S n) #-}

{-# SPECIALIZE instantiate :: Bind DB DB n -> DB n -> DB n #-}

{-# SPECIALIZE bind :: DB (S n) -> Bind DB DB n #-}

{-# SPECIALIZE applyUnder :: (forall m n. Env DB m n -> DB m -> DB n)-> Env DB n1 n2 -> Bind DB DB n1 -> Bind DB DB n2 #-}

----------------------------------------------------------

nf :: DB n -> DB n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (getBody b)))
nf (DApp f a) =
  case whnf idE f of
    DLam b -> nf (instantiate b (whnf idE a)) -- nf here is too slow
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf idE a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a) (nf b) (nf c)

-- invariant: all expressions in the environment are in whnf
whnf :: Env DB m n -> DB m -> DB n
whnf r e@(DVar _) = applyE r e
whnf r e@(DLam _) = applyE r e
whnf r (DApp f a) =
  case whnf r f of
    DLam b -> 
      unbindWith b (\r' b' -> 
         whnf (whnf r a .: r') b')
    f' -> DApp f' (applyE r a)
whnf r e@(DBool b) = DBool b
whnf r (DIf a b c) = 
  case whnf r a of 
    DBool True -> whnf r b
    DBool False -> whnf r c
    a' -> DIf a' (applyE r b) (applyE r c)


eval :: DB n -> DB n
eval = evalr idE 


evalr :: Env DB m n -> DB m -> DB n
evalr r e@(DVar _) = applyE r e
evalr r e@(DLam _) = applyE r e
evalr r (DApp f a) =
  case evalr r f of
    DLam b -> instantiateWith b (evalr r a) evalr
    f' -> f' 
evalr r (DBool b) = DBool b
evalr r (DIf a b c) = 
  case evalr r a of 
    DBool True -> evalr r b
    DBool False -> evalr r c
    a' -> DIf a' (applyE r b) (applyE r c)
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
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n) (getBody b))
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
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (getBody b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
