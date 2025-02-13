{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Auto.Lazy.EnvFelgenhauer (toDB, impl) where

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
    { impl_name = "Auto.Lazy.EnvFelgenhauer",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf zeroE,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==)
    }

data DB n where
  DFree :: IdInt -> DB n  -- free variable
  DBound  :: (Fin n) -> DB n  -- bound variable, uses de Bruijn index
  DLam  :: (Bind DB DB n) -> DB n -- lambda abstraction (includes suspended environment)
  DApp  :: (DB n) -> (DB n) -> DB n -- application

-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (DB n)

instance Eq (Bind DB DB n) where
  b1 == b2 = getBody b1 == getBody b2

instance NFData (DB a) where
  rnf (DFree x) = rnf x
  rnf (DBound i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

instance NFData (Fin n) where
  rnf FZ = ()
  rnf (FS x) = rnf x

instance (Subst v e, Subst v v, forall n. NFData (e n)) => NFData (Bind v e n) where
  rnf b = rnf (unbind b)

----------------------------------------------------------

instance SubstVar DB where
  var = DBound
  {-# INLINEABLE var #-}

instance Subst DB DB where
  applyE s (DBound i) = applyEnv s i
  applyE s (DFree x) = DFree x
  applyE s (DLam b) = DLam (applyE s b)
  applyE s (DApp f a) = DApp (applyE s f) (applyE s a)
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE applyEnv :: Env DB n m -> Fin n -> DB m #-}

{-# SPECIALIZE idE :: Env DB n n #-}

{-# SPECIALIZE (.>>) :: Env DB m n -> Env DB n p -> Env DB m p #-}



{-# SPECIALIZE up :: Env DB n m -> Env DB ('S n) ('S m) #-}

{-# SPECIALIZE unbind :: Bind DB DB n -> DB ('S n) #-}

{-# SPECIALIZE instantiate :: Bind DB DB n -> DB n -> DB n #-}

{-# SPECIALIZE bind :: DB (S n) -> Bind DB DB n #-}

{-# SPECIALIZE applyUnder :: (forall m n. Env DB m n -> DB m -> DB n)-> Env DB n1 n2 -> Bind DB DB n1 -> Bind DB DB n2 #-}

----------------------------------------------------------
-- NOTE: don't normalize the body of lambda expressions yet.
-- wait until conversion back to LC terms

nf :: Env DB m n -> DB m -> DB n
nf r (DFree x)  = DFree x
nf r (DBound x) = applyEnv r x
nf r (DLam b) = DLam (applyE r b)
nf r (DApp f a) =
  let f' = nf r f
      a' = nf r a 
  in case f' of
    DLam b -> instantiateWith b a' nf
    f' -> DApp f' a'

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
    to vs (Var v) = DBound (fromJust (lookup v vs))
    to vs (Lam v b) = DLam (bind b')
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)

-- Convert back from deBruijn to the LC type.
-- can normalize in the process
fromDB :: DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB n -> LC IdInt
    from (IdInt n) (DBound i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DFree x) = Var x
    from n (DLam b) = 
      unbindWith b (\r' b' -> 
        Lam n (from (succ n) 
           (nf (DFree n .: r') b')))
    from n (DApp f a) = App (from n f) (from n a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (DB n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB n -> Doc
ppLC _ (DBound v) = text $ "x" ++ show v
ppLC _ (DFree x) = text (show x)
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
