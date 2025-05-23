{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
-- doesn't use Rebound library
-- doesn't delay substitutions at bind type
-- passes environment argument explicitly and 
module Auto.Manual.Lazy.EnvOnlyV (toDB, impl) where

import Data.SNat as Nat
import Data.Fin
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Lazy.EnvOnlyV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==),
      impl_eval = whnf idE
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
  Bind :: Exp (S n) -> Bind n

bind :: Exp (S n) -> Bind n
bind = Bind

unbind :: Bind n -> Exp (S n)
unbind (Bind a) = a

apply :: Env n m -> Exp n -> Exp m
apply s (DVar i) = s i
apply s (DLam (Bind b)) = 
  DLam (Bind (apply (up s) b))
apply s (DApp f a) = 
  DApp (apply s f) (apply s a)
apply s (DIf a b c) = 
  DIf (apply s a) (apply s b) (apply s c)
apply s (DBool b) = DBool b

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
instantiate (Bind b) v = apply (v .: DVar) b

----------------------------------------------------

nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf idE f of
    DLam b -> nf (instantiate b (whnf idE a))
    f' -> DApp (nf f') (nf a)
nf (DIf a b c) =
  case whnf idE a of 
    DBool True -> nf b
    DBool False -> nf c
    a' -> DIf (nf a') (nf b) (nf c)
nf (DBool b) = DBool b

whnf :: Env m n -> Exp m -> Exp n
whnf r e@(DVar x) = apply r e
whnf r e@(DLam _) = apply r e
whnf r (DApp f a) =
  case whnf r f of
    DLam (Bind b) -> 
        whnf (whnf r a .: idE) b
    f' -> DApp f' (apply r a)
whnf r (DBool b) = DBool b
whnf r (DIf a b c) = case whnf r a of 
  DBool True -> whnf r b
  DBool False -> whnf r c
  a' -> DIf a' (apply r b) (apply r c)

eval :: Env m Z -> Exp m -> Exp Z
eval r (DVar x) = r x
eval r e@(DLam _) = apply r e
eval r (DApp f a) =
  case eval r f of
    DLam (Bind b') -> 
        eval (eval r a .: nil) b'
    _ -> error "type error"
eval r (DBool b) = DBool b
eval r (DIf a b c) = case eval r a of 
  DBool True -> eval r b
  DBool False -> eval r c
  a' -> error "type error"

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
