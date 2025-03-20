{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}

-- | Well-scoped de Bruijn indices 
-- Doesn't use autoenv library, or a bind type
-- but otherwise uses ideas from it
-- with naive substitution, closed terms only
module Auto.Manual.Subst (toDB, impl) where

import Data.Nat
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
    { impl_name = "Auto.Manual.Subst",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==),
      impl_eval = eval
    }

data Exp n where
  DVar :: Fin n -> Exp n
  DLam :: Exp (S n) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n

-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (Exp n)

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

instance NFData (Fin n) where
  rnf FZ = ()
  rnf (FS x) = rnf x

----------------------------------------------------------

type Sub m n = Fin m -> Exp n                   

(.:) :: a -> (Fin m -> a) -> Fin (S m) -> a               -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

up :: Sub m n -> Sub (S m) (S n)                      -- shift
up s = \case
          FZ -> DVar  FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices
      
upZ :: Sub m Z -> Sub (S m) (S Z)                      -- shift
upZ s = \case
          FZ -> DVar FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices


apply :: Sub m n -> Exp m -> Exp n                    -- multi substitutions
apply r (DVar x)      = r x
apply r (DLam b)      = DLam (apply (up r) b)
apply r (DApp a1 a2)  = DApp (apply r a1) (apply r a2)

subst :: Exp n -> Exp (S n) -> Exp n                  -- single substitution
subst v = apply (v .: DVar)

----------------------------------------------------------

type NEnv n = Fin n -> NThunk 

data NThunk where 
  Suspend :: NEnv m -> Exp m -> NThunk

force :: NThunk -> NVal
force (Suspend r a) = cbn r a

data NVal where
  NVLam :: NEnv m -> Exp (S m) -> NVal

cbn :: NEnv m -> Exp m -> NVal
cbn r (DVar x) = force (r x)
cbn r (DLam b) = NVLam r b
cbn r (DApp f a) = 
  case cbn r f of 
     NVLam r' b -> 
       cbn (Suspend r a .: r') b


----------------------------------------------------------

type Env n = Fin n -> Val

data Val where
  VLam :: Env m -> Exp (S m) -> Val

evalE :: (Fin n -> Val) -> Exp n -> Val
evalE r (DVar x) = r x
evalE r (DLam b) = VLam r b
evalE r (DApp f a) = case evalE r f of 
   VLam r' b -> evalE (evalE r a .: r') b

toExp :: Val -> Exp Z
toExp (VLam r e) = DLam (applyE (up (toExp . r)) e)

-- 
applyE :: (Fin n -> Exp m) -> Exp n -> Exp m
applyE r (DVar x) = r x
applyE r (DLam b) = 
  DLam (applyE (up r) b)
applyE r (DApp f a) = 
  DApp (applyE r f) (applyE r a)

-- Evaluate closed expressions (call-by-name)
eval :: Exp Z -> Exp Z
eval (DVar x)   = case x of {}
eval e@(DLam b) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (subst a b)
    f' -> error "DLam expected"

-- weak head reduction (call-by-name)
-- extend eval to open terms
-- but do not reduce under binders (weak reduction)
-- and do not reduce arguments of applications (head reduction)

whnf :: Exp n -> Exp n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (subst a b)
    f' -> DApp f' a    

-- strong reduction, aka normalization (normal-order)
-- reduce under binders
-- reduce arguments applications
nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b)   = DLam (nf b)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (subst a b)
    f' -> DApp (nf f') (nf a)



---------------------------------------------------------
{-
Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. NOTE: input term
must be closed or 'fromJust' will error.
-}

toDB :: LC IdInt -> Exp 'Z
toDB = to []
  where
    to :: [(IdInt, Fin n)] -> LC IdInt -> Exp n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam b'
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)

-- Convert back from deBruijn to the LC type.

fromDB :: Exp n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (succ n)  b)
    from n (DApp f a) = App (from n f) (from n a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (Exp n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> Exp n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 b
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
