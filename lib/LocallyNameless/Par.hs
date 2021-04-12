{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Locally nameless version that uses (typed) parallel substitution for
-- opening vound variables.
module LocallyNameless.Par where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import IdInt
import Impl
import Imports hiding (S, lift)
import qualified Lambda as LC
import qualified Unsafe.Coerce as Unsafe

-- 1. Adding strictness annotations to the datatype definition:
-- lennart: 1.03 s
-- lennart: 132 ms
-- random: 0.807 ms
-- random: 3.64 ms

-- 2. Switching to strongly-typed paralell subst for bound vars
-- lennart: 3.49s
-- random: 5.12 ms

-- Index to keep track of bound variable scope
data Nat = Z | S Nat

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type family Plus n m where
  Plus Z n = n
  Plus (S m) n = S (Plus m n)

instance Show (SNat m) where
  show SZ = "SZ"
  show (SS n) = "(SS " ++ show n ++ ")"

------------------------------------

-- Bound variable index
-- Natural number is # of potential variables in scope
-- Idx Z is a Void type.
-- Idx (S Z) has a single inhabitant: FZ
data Idx :: Nat -> Type where
  FZ :: Idx (S n)
  FS :: Idx n -> Idx (S n)

instance Eq (Idx n) where
  FZ == FZ = True
  (FS n) == (FS m) = n == m
  _ == _ = False

instance Show (Idx n) where
  show FZ = "FZ"
  show (FS n) = "(FS " ++ show n ++ ")"

toInt :: Idx n -> Int
toInt FZ = 0
toInt (FS n) = 1 + toInt n

shift :: SNat m -> Idx n -> Idx (Plus m n)
shift SZ x = x
shift (SS m) x = FS (shift m x)

--------------------------------------------------------------
-- A bound variable multi-substitution. Note that in this implementation
-- even though we only ever replace bound variables with locally closed terms,
-- we still need to renumber (shift) bound variables as we open and close expressions

data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Inc :: !(SNat m) -> Sub a n (Plus m n) --  increment by m
  Cons :: (a m) -> !(Sub a n m) -> Sub a (S n) m --  extend a substitution (like cons)
  (:<>) :: !(Sub a m n) -> !(Sub a n p) -> Sub a m p --  compose substitutions

infixr 9 :<> -- like usual composition  (.)

class SubstC (a :: Nat -> Type) where
  var :: Idx n -> a n
  substBv :: Sub a n m -> a n -> a m

--  Value of the index x in the substitution s
applyS :: SubstC a => Sub a n m -> Idx n -> a m
applyS (Inc m) x = var (shift m x)
applyS (Cons ty _s) FZ = ty
applyS (Cons _ty s) (FS x) = applyS s x
applyS (s1 :<> s2) x = substBv s2 (applyS s1 x)
{-# INLINEABLE applyS #-}

nil :: SubstC a => Sub a n n
nil = Inc SZ
{-# INLINEABLE nil #-}

lift :: SubstC a => Sub a n m -> Sub a (S n) (S m)
lift s = Cons (var FZ) (s :<> Inc (SS SZ))
{-# INLINEABLE lift #-}

single :: SubstC a => a n -> Sub a (S n) n
single t = Cons t (Inc SZ)
{-# INLINEABLE single #-}

incSub :: Sub a n (S n)
incSub = Inc (SS SZ)
{-# INLINEABLE incSub #-}

-- smart constructor for composition
comp :: SubstC a => Sub a m n -> Sub a n p -> Sub a m p
comp (Inc SZ) s = s
comp (Inc (SS n)) (Cons t s) = comp (Inc n) s
comp s (Inc SZ) = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (substBv s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

instance (forall n. NFData (a n)) => NFData (Sub a m1 m2) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

instance (forall n. NFData (a n)) => NFData (Bind a m) where
  rnf (Bind a) = rnf a

instance NFData (Idx a) where
  rnf FZ = ()
  rnf (FS s) = rnf s

instance NFData (SNat a) where
  rnf SZ = ()
  rnf (SS s) = rnf s

--------------------------------------------------------------
--------------------------------------------------------------

data Bind a n where
  Bind :: !(a (S n)) -> Bind a n

-- create a binding by "abstracting a variable"
bind :: a (S n) -> Bind a n
bind x = Bind x
{-# INLINEABLE bind #-}

unbind :: SubstC a => Bind a n -> a (S n)
unbind (Bind a) = a
{-# INLINEABLE unbind #-}

substBvBind :: SubstC a => Sub a n m -> Bind a n -> Bind a m
substBvBind s2 (Bind e) = Bind (substBv (lift s2) e)
{-# INLINEABLE substBvBind #-}

instance (SubstC a, Eq (a (S n))) => Eq (Bind a n) where
  (Bind x) == (Bind y) = x == y

-- Exp Z is  locally closed terms
data Exp (n :: Nat) where
  Var_b :: !(Idx n) -> Exp n
  Var_f :: !IdInt -> Exp n
  Abs :: Bind Exp n -> Exp n
  App :: !(Exp n) -> !(Exp n) -> Exp n
  deriving (Generic)

-- instance Show (Exp n) where

open :: Bind Exp Z -> Exp Z -> Exp Z
open (Bind e) u = substBv (single u) e

instance SubstC Exp where
  var = Var_b

  substBv s (Var_b i) = applyS s i
  substBv s (Var_f x) = Var_f x
  substBv s (Abs b) = Abs (substBvBind s b)
  substBv s (App a b) = App (substBv s a) (substBv s b)

-- if n2 is greater than n1 increment it. Otherwise just return it.
cmpIdx :: Idx (S n) -> Idx n -> Idx (S n)
cmpIdx n1 n2 =
  case (n1, n2) of
    (FS m, FZ) -> FZ
    (FS m, FS n) -> FS (cmpIdx m n)
    (FZ, FZ) -> FZ
    (FZ, FS n) -> FS FZ

-- Create a new "bound index" from a free variable
-- The index starts at FZ and comes from a larger scope
-- All variables that are less than the new index must be incremented.
close_exp_wrt_exp_rec :: Idx (S n) -> IdInt -> Exp n -> Exp (S n)
close_exp_wrt_exp_rec n1 x1 e1 =
  case e1 of
    Var_f x2 -> if (x1 == x2) then (Var_b n1) else (Var_f x2)
    -- variables that are greater than the binding level n1 need to be incremented
    -- because we are adding another binding
    Var_b n2 -> Var_b (cmpIdx n1 n2)
    Abs (Bind e2) -> Abs (Bind (close_exp_wrt_exp_rec (FS n1) x1 e2))
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)

close :: IdInt -> Exp Z -> Bind Exp Z
close x e = Bind (close_exp_wrt_exp_rec FZ x e)

{-
openBindRec :: Int -> Exp -> Bind Exp -> Bind Exp
openBindRec = undefined

open :: Bind Exp -> Exp -> Exp
open e u = undefined -- open_exp_wrt_exp_rec 0 u e

closeBindRec :: Int -> IdInt -> Bind Exp -> Bind Exp
closeBindRec = undefined

close :: IdInt -> Exp -> Bind Exp
close x1 e1 = undefined -- close_exp_wrt_exp_rec 0 x1 e1

fvBind :: Bind Exp -> Set IdInt
fvBind = undefined
-}

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.Par",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

{-
toDB :: LC.LC IdInt -> DB Z
toDB = to []
  where to :: [(IdInt, Idx n)] -> LC IdInt ->  DB n
        to vs (Var v)   = DVar (fromJust (lookup v vs))
        to vs (Lam v b) = DLam (bind b') where
             b' = to ((v,FZ):mapSnd FS vs) b
        to vs (App f a) = DApp (to vs f) (to vs a)
-

fromDB :: DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)
-}

toDB :: LC.LC IdInt -> Exp Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC.LC IdInt -> Exp n
    to vs (LC.Var v@(IdInt i)) = maybe (Var_f v) Var_b (lookup v vs)
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
    from n (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | toInt i < 0 = LC.Var (IdInt $ toInt i)
      | toInt i >= n = LC.Var (IdInt $ toInt i)
      | otherwise = LC.Var (IdInt (n - (toInt i) -1))
    from n (Abs (Bind b)) = LC.Lam n (from (succ n) b)
    from n (App f a) = LC.App (from n f) (from n a)

aeq :: Exp n -> Exp n -> Bool
aeq (Var_b i) (Var_b j) = i == j
aeq (Var_f i) (Var_f j) = i == j
aeq (Abs (Bind a)) (Abs (Bind b)) = aeq a b
aeq (App a b) (App c d) = aeq a c && aeq b d

instance NFData (Exp n) where
  rnf (Var_b i) = rnf i
  rnf (Var_f i) = rnf i
  rnf (Abs b) = rnf b
  rnf (App a b) = rnf a `seq` rnf b

-- no bound variables to weaken.
weaken :: forall m n. SNat m -> Exp n -> Exp (Plus n m)
weaken m (Var_b i) = Var_b (weakenIdx m i)
weaken m (Var_f x) = Var_f x
weaken m (Abs (Bind a)) = Abs (bind (weaken m a))
weaken m (App a b) = App (weaken m a) (weaken m b)

weakenIdx :: SNat m -> Idx n -> Idx (Plus n m)
weakenIdx _ FZ = FZ
weakenIdx m (FS n) = FS (weakenIdx m n)

-- free variable substitution
subst :: Exp Z -> IdInt -> Exp Z -> Exp Z
subst u y e = subst0 SZ e
  where
    subst0 :: SNat n -> Exp n -> Exp n
    subst0 n e = case e of
      (Var_b n) -> Var_b n
      (Var_f x) -> (if x == y then weaken n u else (Var_f x))
      (Abs (Bind e1)) -> Abs (Bind (subst0 (SS n) e1))
      (App e1 e2) -> App (subst0 n e1) (subst0 n e2)

fv :: Exp n -> Set IdInt
fv e =
  case e of
    (Var_b nat) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs (Bind e)) -> fv e
    (App e1 e2) -> fv e1 `Set.union` fv e2

{-
open_exp_wrt_exp_rec :: Int -> Exp -> Exp -> Exp
open_exp_wrt_exp_rec k u e =
  case e of
    (Var_b n) ->
      case compare n k of
        LT -> Var_b n
        EQ -> u
        GT -> Var_b (n - 1)
    (Var_f x) -> Var_f x
    (Abs e) -> Abs (openBindRec (k + 1) u e)
    (App e1 e2) ->
      App
        (open_exp_wrt_exp_rec k u e1)
        (open_exp_wrt_exp_rec k u e2)

open_exp_wrt_map_rec :: IM.IntMap IdInt -> Exp -> Exp
open_exp_wrt_map_rec k e =
  case e of
    (Var_b n) ->
      case compare n k of
        LT -> Var_b n
        EQ -> u
        GT -> Var_b (n - 1)
    (Var_f x) -> Var_f x
    (Abs e) -> Abs (openRec (k + 1) e)
    -- need to increment the domain of all
    (App e1 e2) ->
      App
        (open_exp_wrt_map_rec k e1)
        (open_exp_wrt_map_rec k e2)

close_exp_wrt_exp_rec :: Int -> IdInt -> Exp -> Exp
close_exp_wrt_exp_rec n1 x1 e1 =
  case e1 of
    Var_f x2 -> if (x1 == x2) then (Var_b n1) else (Var_f x2)
    Var_b n2 -> if (n2 < n1) then (Var_b n2) else (Var_b (1 + n2))
    Abs e2 -> Abs (closeBindRec (1 + n1) x1 e2)
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
-}

type N a = State IdInt a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfd :: Exp Z -> Exp Z
nfd e = State.evalState (nf' e) firstBoundId

nf' :: Exp Z -> N (Exp Z)
nf' e@(Var_f _) = return e
nf' e@(Var_b _) = error "should not reach this"
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
whnf :: Exp Z -> N (Exp Z)
whnf e@(Var_f _) = return e
whnf e@(Var_b _) = error "BUG"
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (open b a)
    _ -> return $ App f' a

-- Fueled version

nfi :: Int -> Exp Z -> Maybe (Exp Z)
nfi n e = State.evalStateT (nfi' n e) firstBoundId

type NM a = State.StateT IdInt Maybe a

nfi' :: Int -> (Exp Z) -> NM (Exp Z)
nfi' 0 _ = State.lift Nothing
nfi' n e@(Var_f _) = return e
nfi' n e@(Var_b _) = error "should not reach this"
nfi' n (Abs e) = do
  x <- newVar
  e' <- nfi' (n - 1) (open e (Var_f x))
  return $ Abs (close x e')
nfi' n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Abs b -> nfi' (n - 1) (open b a)
    _ -> App <$> nfi' (n - 1) f' <*> nfi' (n -1) a

-- Compute the weak head normal form.
whnfi :: Int -> Exp Z -> NM (Exp Z)
whnfi 0 _ = State.lift Nothing
whnfi n e@(Var_f _) = return e
whnfi n e@(Var_b _) = error "BUG"
whnfi n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> whnfi (n -1) (open b a)
    _ -> return $ App f' a