{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
-- doesn't use autoenv library, but creates 
-- a Bind type.
module Auto.Manual.Bind (toDB, impl) where

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
    { impl_name = "Auto.Manual.Bind",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==)
    }


data Exp n where
  DVar :: (Fin n) -> Exp n
  DLam :: (Bind n) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n

deriving instance Eq (Exp n)

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

instance NFData (Fin n) where
  rnf FZ = ()
  rnf (FS x) = rnf x

instance NFData (Bind n) where
  rnf b = rnf (unbind b)
  
instance Eq (Bind n) where
  b1 == b2 = unbind b1 == unbind b2

----------------------------------------------------------

type Env n m = Fin n -> Exp m

data Bind n where
  Bind :: (Fin m -> Exp n) -> Exp (S m) -> Bind n

bind :: Exp (S n) -> Bind n
bind = Bind DVar

unbind :: Bind n -> Exp (S n)
unbind (Bind r a) = apply (up r) a

apply :: Env n m -> Exp n -> Exp m
apply s (DVar i) = s i
apply s (DLam (Bind r b)) = 
  DLam (Bind (s .>> r) b)
apply s (DApp f a) = 
  DApp (apply s f) (apply s a)

idE :: Env m m
idE = DVar

nil :: Fin Z -> a
nil = \case

(.:) :: a -> (Fin m -> a) -> Fin (S m) -> a               -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

(.>>) :: Env m n -> Env p m -> Env p n
r .>> s = apply r . s

up :: Env m n -> Env (S m) (S n)             -- shift
up s = \case
          FZ -> DVar  FZ                     -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)    -- shift other indices

instantiate :: Bind n -> Exp n -> Exp n
instantiate (Bind r b) v = apply (v .: r) b

----------------------------------------------------------
-- Explicit CBN evaluation

data Thunk where
  Sus :: (Fin n -> Thunk) -> Exp n -> Thunk

force :: Thunk -> Exp Z
force (Sus r a) = cbn r a

cbn :: (Fin n -> Thunk) -> Exp n -> Exp Z 
cbn r (DVar x) = force (r x)
cbn r (DLam b) = apply (force . r) (DLam b)
cbn r (DApp f a) = case cbn r f of 
   DLam (Bind r' b) -> 
    cbn (Sus r a .: (Sus nil . r')) b

----------------------------------------------------------
-- evaluation without env argument

eval :: Exp Z -> Exp Z
eval (DVar x) = case x of {}
eval (DLam b) = DLam b
eval (DApp f a) = case eval f of 
   DLam b ->
      eval (instantiate b (eval a))

-- evaluation with env argument
evalE :: Env m Z -> Exp m -> Exp Z
evalE r (DVar x) = r x
evalE r (DLam (Bind r' b)) = DLam (Bind (r .>> r') b)
evalE r (DApp f a) = case evalE r f of 
   DLam (Bind r' b) -> evalE (evalE r a .: r') b
   _ -> error ""

----------------------------------------------------

nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf idE f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)

whnf :: Env m n -> Exp m -> Exp n
whnf r e@(DVar _) = apply r e
whnf r e@(DLam _) = apply r e
whnf r (DApp f a) =
  case whnf r f of
    DLam (Bind r' b') -> 
        whnf (apply r a .: r') b'
    f' -> DApp f' (apply r a)

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
    to vs (Lam v b) = DLam (bind b')
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
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (Exp n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> Exp n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
