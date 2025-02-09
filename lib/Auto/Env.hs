{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Auto.Env (toDB, impl) where

import AutoEnv
import AutoEnv.Bind.Single
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
    { impl_name = "Auto.Env",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf zeroE,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==)
    }


data DB n where
  DVar :: !(Fin n) -> DB n
  DLam :: !(Bind DB DB n) -> DB n
  DApp :: !(DB n) -> !(DB n) -> DB n

-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (DB n)

instance Eq (Bind DB DB n) where
  b1 == b2 = getBody b1 == getBody b2

instance NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

instance NFData (Fin n) where
  rnf FZ = ()
  rnf (FS x) = rnf x

instance (Subst v e, forall n. NFData (e n)) => NFData (Bind v e n) where
  rnf b = rnf (unbind b)

----------------------------------------------------------
-- uses the SubstScoped library
instance SubstVar DB where
  var = DVar
  {-# INLINEABLE var #-}

instance Subst DB DB where
  applyE s (DVar i) = applyEnv s i
  applyE s (DLam b) = DLam (applyE s b)
  applyE s (DApp f a) = DApp (applyE s f) (applyE s a)
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE applyEnv :: Env DB n m -> Fin n -> DB m #-}

{-# SPECIALIZE idE :: Env DB n n #-}

{-# SPECIALIZE (.>>) :: Env DB m n -> Env DB n p -> Env DB m p #-}

{-# SPECIALIZE singletonE :: DB n -> Env DB (S n) n #-}

{-# SPECIALIZE up :: Env DB n m -> Env DB ('S n) ('S m) #-}

{-# SPECIALIZE unbind :: Bind DB DB n -> DB ('S n) #-}

{-# SPECIALIZE instantiate :: Bind DB DB n -> DB n -> DB n #-}

{-# SPECIALIZE bind :: DB (S n) -> Bind DB DB n #-}

{-# SPECIALIZE applyUnder :: (forall m n. Env DB m n -> DB m -> DB n)-> Env DB n1 n2 -> Bind DB DB n1 -> Bind DB DB n2 #-}

----------------------------------------------------------
-- TODO: update with more efficient version
nf :: Env DB m n -> DB m -> DB n
nf ctx (DVar x) = applyEnv ctx x 
nf ctx (DLam b) = 
  let b' = unbind b in
  let b'' = nf (up ctx) b' in
  DLam (bind b'')
nf ctx (DApp f a) =
  case whnf ctx f of
    DLam b -> nf idE (instantiate b (applyE ctx a))
    f' -> DApp (nf idE f') (nf ctx a)

whnf :: Env DB m n -> DB m -> DB n
whnf r e@(DVar _) = applyE r e
whnf r e@(DLam _) = applyE r e
whnf r (DApp f a) =
  case whnf r f of
    DLam b -> whnf idE (instantiate b (applyE r a))
    f' -> DApp f' (applyE r a)

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

-- Convert back from deBruijn to the LC type.

fromDB :: DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (DB n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
