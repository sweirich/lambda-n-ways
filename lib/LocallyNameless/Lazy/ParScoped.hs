{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Locally nameless version that uses (typed) parallel substitution for
-- opening vound variables.
-- Like DeBruijn.Par.P, but well-scoped
module LocallyNameless.Lazy.ParScoped (impl, substFv, fv) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import Util.Nat
  ( Idx (..),
    Nat (..),
    Plus,
    SNat (..),
    cmpIdx,
    shift,
    toInt,
    weakenIdxR,
  )
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

-- 0. (Ott) Adding strictness annotations to the datatype definition:
-- lennart: 1.03 s
-- lennart: 132 ms
-- random: 0.807 ms
-- random: 3.64 ms

-- 1. (ParScoped) Switching to strongly-typed parallel subst for bound vars
-- lennart: 3.49s
-- random: 5.12 ms

--------------------------------------------------------------

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.Lazy.ParScoped",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

-- Exp Z is  locally closed terms
data Exp (n :: Nat) where
  Var_b :: (Idx n) -> Exp n
  Var_f :: IdInt -> Exp n
  Abs :: (Bind Exp n) -> Exp n
  App :: (Exp n) -> (Exp n) -> Exp n
  deriving (Generic)

instance NFData (Exp n)

deriving instance (Eq (Exp n))

---------------------------------------------------

-- free variable substitution
substFv :: Exp 'Z -> IdInt -> Exp 'Z -> Exp 'Z
substFv u y = subst0 SZ
  where
    subst0 :: SNat n -> Exp n -> Exp n
    subst0 n e = case e of
      (Var_b _) -> e
      (Var_f x) -> (if x == y then weaken n u else e)
      (Abs (Bind e1)) -> Abs (Bind (subst0 (SS n) e1))
      (App e1 e2) -> App (subst0 n e1) (subst0 n e2)

-- no bound variables to weaken.
-- This is an identity function, so could also use
-- unsafeCoerce for this implementation
weaken :: forall m n. SNat m -> Exp n -> Exp (Plus n m)
weaken _m (Var_b i) = Var_b (weakenIdxR @m i)
weaken _m (Var_f x) = Var_f x
weaken m (Abs (Bind a)) = Abs (bind (weaken m a))
weaken m (App a b) = App (weaken m a) (weaken m b)

fv :: Exp n -> Set IdInt
fv e =
  case e of
    (Var_b _) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs (Bind e0)) -> fv e0
    (App e1 e2) -> fv e1 `Set.union` fv e2

---------------------------------------------------

-- A bound variable multi-substitution. Note that in this implementation
-- even though we only ever replace bound variables with locally closed terms,
-- we still need to renumber (shift) bound variables as we open and close expressions

data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Inc :: !(SNat m) -> Sub a n (Plus m n) --  increment by m
  Cons :: (a m) -> !(Sub a n m) -> Sub a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Sub a m n) -> !(Sub a n p) -> Sub a m p --  compose substitutions

infixr 9 :<> -- like usual composition  (.)

class SubstC (a :: Nat -> Type) where
  var :: Idx n -> a n
  subst :: Sub a n m -> a n -> a m

--  Value of the index x in the substitution s
applyS :: SubstC a => Sub a n m -> Idx n -> a m
applyS (Inc m) x = var (shift m x)
applyS (Cons ty _s) FZ = ty
applyS (Cons _ty s) (FS x) = applyS s x
applyS (s1 :<> s2) x = subst s2 (applyS s1 x)
{-# INLINEABLE applyS #-}

lift :: SubstC a => Sub a n m -> Sub a ('S n) ('S m)
lift s = Cons (var FZ) (s :<> Inc (SS SZ))
{-# INLINEABLE lift #-}

single :: SubstC a => a n -> Sub a ('S n) n
single t = Cons t (Inc SZ)
{-# INLINEABLE single #-}

instance (forall n. NFData (a n)) => NFData (Sub a m1 m2) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

instance (forall n. NFData (a n)) => NFData (Bind a m) where
  rnf (Bind a) = rnf a

--------------------------------------------------------------

data Bind a n where
  Bind :: !(a ('S n)) -> Bind a n

instance (Eq (a ('S n))) => Eq (Bind a n) where
  x == y = unbind x == unbind y

-- create a binding by "abstracting a variable"
bind :: a ('S n) -> Bind a n
bind x = Bind x
{-# INLINEABLE bind #-}

unbind :: Bind a n -> a ('S n)
unbind (Bind a) = a
{-# INLINEABLE unbind #-}

substBvBind :: SubstC a => Sub a n m -> Bind a n -> Bind a m
substBvBind s2 (Bind e) = Bind (subst (lift s2) e)
{-# INLINEABLE substBvBind #-}

--------------------------------------------------------------

open :: Bind Exp 'Z -> Exp 'Z -> Exp 'Z
open (Bind e) u = subst (single u) e

instance SubstC Exp where
  var = Var_b

  subst s (Var_b i) = applyS s i
  subst _s (Var_f x) = Var_f x
  subst s (Abs b) = Abs (substBvBind s b)
  subst s (App a b) = App (subst s a) (subst s b)

-- Create a new "bound index" from a free variable
-- The index starts at FZ and comes from a larger scope
-- All variables that are less than the new index must be incremented.
close_exp_wrt_exp_rec :: Idx ('S n) -> IdInt -> Exp n -> Exp ('S n)
close_exp_wrt_exp_rec n1 x1 e1 =
  case e1 of
    Var_f x2 -> if (x1 == x2) then (Var_b n1) else (Var_f x2)
    -- variables that are greater than the binding level n1 need to be incremented
    -- because we are adding another binding
    Var_b n2 -> Var_b (cmpIdx n1 n2)
    Abs (Bind e2) -> Abs (Bind (close_exp_wrt_exp_rec (FS n1) x1 e2))
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)

close :: IdInt -> Exp 'Z -> Bind Exp 'Z
close x e = Bind (close_exp_wrt_exp_rec FZ x e)

--------------------------------------------------------------------

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

--------------------------------------------------------------------

toDB :: LC.LC IdInt -> Exp 'Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC.LC IdInt -> Exp n
    to vs (LC.Var v) = maybe (Var_f v) Var_b (lookup v vs)
    to vs (LC.Lam x b) = Abs (bind b')
      where
        b' = to ((x, FZ) : mapSnd FS vs) b
    to vs (LC.App f a) = App (to vs f) (to vs a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

fromDB :: Exp n -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC.LC IdInt
    from _n (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | toInt i < 0 = LC.Var (IdInt $ toInt i)
      | toInt i >= n = LC.Var (IdInt $ toInt i)
      | otherwise = LC.Var (IdInt (n - (toInt i) -1))
    from n (Abs (Bind b)) = LC.Lam n (from (succ n) b)
    from n (App f a) = LC.App (from n f) (from n a)
