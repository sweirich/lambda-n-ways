{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
-- doesn't use Rebound library, but creates 
-- a Bind type. (lazy representation)
-- delays substitution using Bind but doesn't 
-- pass it explicitly
module Auto.Manual.Lazy.BindV (toDB, impl) where

import Data.SNat as Nat
import Data.Fin as Fin
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
    { impl_name = "Auto.Manual.Lazy.BindV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==),
      impl_eval = eval
    }


data Exp n where
  DVar :: (Fin n) -> Exp n
  DLam :: (Bind n) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n
  DBool :: Bool -> Exp n
  DIf :: Exp n -> Exp n -> Exp n -> Exp n

deriving instance Eq (Exp n)

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (DBool b) = rnf b

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
  DLam (Bind (r .>> s) b)
apply s (DApp f a) = 
  DApp (apply s f) (apply s a)
apply s (DIf a b c) = DIf (apply s a) (apply s b) (apply s c)
apply s (DBool b) = DBool b

idE :: Env m m
idE = DVar

nil :: Fin Z -> a
nil = \case

(.:) :: a -> (Fin m -> a) -> Fin (S m) -> a               -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

(.>>) :: Env p m -> Env m n -> Env p n
r .>> s = apply s . r


shift :: Env m (S m)
shift = \x -> DVar (Fin.shiftN Nat.s1 x)

up :: Env m n -> Env (S m) (S n)             -- shift
up s = DVar FZ .: (s .>> shift)

instantiate :: Bind n -> Exp n -> Exp n
instantiate (Bind r b) v = apply (v .: r) b

----------------------------------------------------------
-- evaluation without env argument

eval :: Exp Z -> Exp Z
eval (DVar x) = case x of {}
eval (DLam b) = DLam b
eval (DApp f a) = 
  case eval f of 
    DLam b ->
      eval (instantiate b (eval a))
    _ -> error "type error"
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval b
    DBool False -> eval c
    _ -> error "type error"

----------------------------------------------------

nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b (whnf a))
    f' -> DApp (nf f') (nf a)
nf (DIf a b c) =
  case whnf a of 
    DBool True -> nf b
    DBool False -> nf c
    a' -> DIf (nf a') (nf b) (nf c)
nf (DBool b) = DBool b


whnf :: Exp n -> Exp n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b (whnf a))
    f' -> DApp f' a
whnf (DBool b) = DBool b
whnf (DIf a b c) = case whnf a of 
  DBool True -> whnf b
  DBool False -> whnf c
  a' -> DIf a' b c

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
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
    to vs (Bool b) = DBool b

-- Convert back from deBruijn to the LC type.

fromDB :: Exp n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DIf a b c) = If (from n a) (from n b) (from n c)
    from n (DBool b) = Bool b

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------
