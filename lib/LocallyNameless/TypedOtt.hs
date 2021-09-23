{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- Then with types addded to make sure that terms stay locally closed (when they need to be)
module LocallyNameless.TypedOtt (impl, substFv, fv) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import Data.Type.Equality (type (:~:) (..))
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import Util.Nat
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

-- 0. (Ott) Original
-- lennart: 1.03s
-- random: 0.807 ms

-- 1. (TypedOtt) Well-typed (slows it down)
-- lennart: 1.43s
-- random: 1.8ms

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.TypedOtt",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

-- Exp Z is  locally closed terms
data Exp (n :: Nat) where
  Var_b :: !(Idx n) -> Exp n
  Var_f :: !IdInt -> Exp n
  Abs :: !(Bind Exp n) -> Exp n
  App :: !(Exp n) -> !(Exp n) -> Exp n
  deriving (Generic)

deriving instance (Eq (Exp n))

instance NFData (Exp n)

--------------------------------------------------------------

-- free variable substitution
substFv :: Exp 'Z -> IdInt -> Exp 'Z -> Exp 'Z
substFv u y = subst0 SZ
  where
    subst0 :: forall n. SNat n -> Exp n -> Exp n
    subst0 k e0 = case e0 of
      (Var_b n) -> Var_b n
      (Var_f x) -> (if x == y then weaken @n u else (Var_f x))
      (Abs b) -> Abs (bind (subst0 (SS k) (unbind b)))
      (App e1 e2) -> App (subst0 @n k e1) (subst0 @n k e2)

-- no bound variables to weaken.
weaken :: forall m n. Exp n -> Exp (Plus n m)
weaken (Var_b x) = Var_b (weakenIdxR @m x)
weaken (Var_f x) = Var_f x
weaken (Abs (Bind b)) = Abs (Bind (weaken @m b))
weaken (App a b) = App (weaken @m a) (weaken @m b)

fv :: Exp n -> Set IdInt
fv e =
  case e of
    (Var_b _) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs b) -> fv (unbind b)
    (App e1 e2) -> fv e1 `Set.union` fv e2

instance (forall n. NFData (a n)) => NFData (Bind a m) where
  rnf (Bind a) = rnf a

--------------------------------------------------------------
--------------------------------------------------------------

-- Locally nameless simplification.
-- when we open, we only replace with locally closed terms
-- and we only use open for variables with a single bound variable.
-- This means that we do *not* need to shift as much.

data Bind a k where
  Bind :: !(a ('S k)) -> Bind a k

-- create a binding by "abstracting a variable"
bind :: a ('S k) -> Bind a k
bind = Bind
{-# INLINEABLE bind #-}

unbind :: forall k. Bind Exp k -> Exp ('S k)
unbind (Bind a) = a -- multi_open_exp_wrt_exp_rec ss a
{-# INLINEABLE unbind #-}

instance (Eq (Exp ('S n))) => Eq (Bind Exp n) where
  b1 == b2 = unbind b1 == unbind b2

open_exp_wrt_exp_rec :: forall n. SNat n -> Exp 'Z -> Exp ('S n) -> Exp n
open_exp_wrt_exp_rec k u e =
  case e of
    (Var_b (n :: Idx ('S n))) ->
      case compareIdx k n of
        Just i -> Var_b i
        Nothing -> weaken u
    (Var_f x) -> Var_f x
    (Abs (Bind b)) -> Abs (Bind (open_exp_wrt_exp_rec (SS k) u b))
    (App e1 e2) ->
      App
        (open_exp_wrt_exp_rec k u e1)
        (open_exp_wrt_exp_rec k u e2)

open :: Bind Exp 'Z -> Exp 'Z -> Exp 'Z
open (Bind e) u = f
  where
    f = open_exp_wrt_exp_rec SZ u e

close_exp_wrt_exp_rec :: Idx ('S n) -> IdInt -> Exp n -> Exp ('S n)
close_exp_wrt_exp_rec n1 x1 e1 =
  case e1 of
    Var_f x2 -> if (x1 == x2) then (Var_b n1) else (Var_f x2)
    Var_b n2 -> Var_b (weakenIdx n2)
    Abs b -> Abs (bind (close_exp_wrt_exp_rec (FS n1) x1 (unbind b)))
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)

close :: IdInt -> Exp 'Z -> Bind Exp 'Z
close x e = bind (close_exp_wrt_exp_rec FZ x e)

toDB :: LC.LC IdInt -> Exp 'Z
toDB = to SZ []
  where
    to :: SNat n -> [(IdInt, Idx n)] -> LC.LC IdInt -> Exp n
    to _ vs (LC.Var v) = maybe (Var_f v) Var_b (lookup v vs)
    to k vs (LC.Lam x b) = Abs (bind b')
      where
        b' = to (SS k) ((x, FZ) : mapSnd FS vs) b
    to k vs (LC.App f a) = App (to k vs f) (to k vs a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

fromDB :: Exp n -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC.LC IdInt
    from _ (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | toInt i < 0 = LC.Var (IdInt $ toInt i)
      | toInt i >= n = LC.Var (IdInt $ toInt i)
      | otherwise = LC.Var (IdInt (n - (toInt i) -1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)

----------------------------------------------------------------

type N a = State IdInt a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfd :: Exp 'Z -> Exp 'Z
nfd e = State.evalState (nf' e) v
  where
    v = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

nf' :: Exp 'Z -> N (Exp 'Z)
nf' e@(Var_f _) = return e
nf' (Abs b) = do
  x <- newVar
  b' <- nf' (open b (Var_f x))
  return $ Abs (close x b')
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Abs b -> nf' (open b a)
    _ -> App <$> nf' f' <*> nf' a

-- Compute the weak head normal form.
whnf :: Exp 'Z -> N (Exp 'Z)
whnf e@(Var_f _) = return e
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (open b a)
    _ -> return $ App f' a

-- Fueled version

nfi :: Int -> Exp 'Z -> Stats.M (Exp 'Z)
nfi n e = State.evalStateT (nfi' n e) v
  where
    v = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

type NM a = State.StateT IdInt Stats.M a

nfi' :: Int -> (Exp 'Z) -> NM (Exp 'Z)
nfi' 0 _ = State.lift Stats.done
nfi' _ e@(Var_f _) = return e
nfi' n (Abs e) = do
  x <- newVar
  e' <- nfi' (n - 1) (open e (Var_f x))
  return $ Abs (close x e')
nfi' n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Abs b -> State.lift Stats.count >> nfi' (n - 1) (open b a)
    _ -> App <$> nfi' (n - 1) f' <*> nfi' (n -1) a

-- Compute the weak head normal form.
whnfi :: Int -> Exp 'Z -> NM (Exp 'Z)
whnfi 0 _ = State.lift Stats.done
whnfi _ e@(Var_f _) = return e
whnfi _ e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (open b a)
    _ -> return $ App f' a