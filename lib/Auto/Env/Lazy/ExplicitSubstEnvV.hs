{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
-- Uses autoenv library
-- explicit substitutions in arbitrary syntax nodes
-- passes environment explicitly while evaluating
module Auto.Env.Lazy.ExplicitSubstEnvV (toDB, impl) where

import AutoEnv
import Data.SNat as Nat
import Data.Fin
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Env.Lazy.ExplicitSubstEnvV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==),
      impl_eval = whnf' idE 
    }


data Exp n where
  DVar :: (Fin n) -> Exp n
  DLam :: (Exp (S n)) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n
  DBool :: Bool -> Exp n
  DIf :: Exp n -> Exp n -> Exp n -> Exp n
  Sub :: Env Exp m n -> Exp m -> Exp n


instance Eq (Exp n) where
  DVar x == DVar y = x == y
  DLam t == DLam u = t == u
  DApp t1 t2 == DApp u1 u2 = t1 == u1 && t2 == u2
  DBool x == DBool y = x == y
  DIf t1 t2 t3 == DIf u1 u2 u3 = t1 == u1 && t2 == u2 && t3 == u3
  Sub s t == Sub r u = applyE s t == applyE r u
  _ == _ = False

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (DBool b) = rnf b
  rnf (Sub r t) = rnf (applyE r t)
----------------------------------------------------------

{-
type Env n m = Fin n -> Exp m
-}
-- Apply a substitution to a term; composing 
-- with any explicit substitutions and pushing 
-- them one level down the syntax tree
-- Invariant: result of apply is *not* a Sub.
instance SubstVar Exp where 
  var = DVar
  {-# INLINEABLE var #-}
instance Subst Exp Exp where
  applyE :: Env Exp n m -> Exp n -> Exp m
  applyE s (DVar i) = applyEnv s i
  applyE s (DLam b) = 
    DLam (Sub (up s) b)
  applyE s (DApp f a) = 
    DApp (Sub s f) (Sub s a)
  applyE s (DIf a b c) = DIf (Sub s a) (Sub s b) (Sub s c)
  applyE s (DBool b) = DBool b
  applyE s (Sub r t) = applyE (r .>> s) t
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE applyEnv :: Env Exp n m -> Fin n -> Exp m #-}

{-# SPECIALIZE idE :: Env Exp n n #-}

{-# SPECIALIZE (.>>) :: Env Exp m n -> Env Exp n p -> Env Exp m p #-}
----------------------------------------------------

-- result of nf is not a Sub
nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (nf b)
nf (DApp f a) =
  case whnf' idE f of
    DLam b -> nf (applyE (singletonE (nf a)) b)
    f' -> DApp (nf f') (nf a)
nf (DIf a b c) =
  case whnf' idE a of 
    DBool True -> nf b
    DBool False -> nf c
    a' -> DIf (nf a') (nf b) (nf c)
nf (DBool b) = DBool b
nf (Sub r t) = nf (applyE r t)


whnf' :: Env Exp m n -> Exp m -> Exp n
whnf' r e@(DVar x) = applyE r e
whnf' r e@(DLam _) = applyE r e
whnf' r (DApp f a) =
  case whnf' r f of
    DLam b' -> 
        whnf' (singletonE (whnf' r a)) b'
    f' -> 
      -- ok to leave Sub around a as top-level is App
      DApp f' (Sub r a)
whnf' r (DBool b) = DBool b
whnf' r (DIf a b c) = case whnf' r a of 
  DBool True -> whnf' r b
  DBool False -> whnf' r c
  a' -> DIf a' (Sub r b) (Sub r c)
whnf' r (Sub s t) = whnf' (s .>> r) t



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
    from n (DLam b) = Lam n (from (Prelude.succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DIf a b c) = If (from n a) (from n b) (from n c)
    from n (DBool b) = Bool b
    from n (Sub s b) = from n (applyE s b)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------
