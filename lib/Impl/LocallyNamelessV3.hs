-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- Then with types addded, and multi substitutions
-- And caching openning substitutions at binders
-- and caching closing substitutions at binders
-- and removing types so we can use ints instead of unary nats
module Impl.LocallyNamelessV3 (impl) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import Data.Type.Equality
import IdInt
import Impl
import Imports hiding (S, lift)
import qualified Lambda as LC
import qualified Unsafe.Coerce as Unsafe

-- 0. Original
-- lennart: 1.03s
-- random: 0.807 ms

-- 1. Well-typed (slows it down)
-- lennart: 1.43s
-- random: 1.8ms

-- 2. Well-typed multisubst

-- 3. Combo multisubst for open
-- lennart: 4.10 ms (wow!)
-- random: 1.46 ms (a little slow)

-- 4. Combo multisubst for open & close
-- lennart: 3.05 ms
-- random: 0.135 ms

-- 5. back to ints, with some general cleanup
-- lennart: 2.76 ms
-- random: 0.116 ms
-------------------------------------------------------------------

instance (NFData a) => NFData (Bind a) where
  rnf (BindOpen k s a) = rnf k `seq` rnf s `seq` rnf a
  rnf (Bind a) = rnf a
  rnf (BindClose k v a) =
    rnf k
      `seq` rnf v
      `seq` rnf a

--------------------------------------------------------------
--------------------------------------------------------------

-- Locally nameless simplification.
-- We only use substBv to implement open
-- when we open, we only replace with locally closed terms
-- and we only use open for variables with a single bound variable.
-- This means that we do *not* need to shift as much.

data Bind a where
  Bind :: !a -> Bind a
  BindOpen :: !Int -> ![Exp] -> !a -> Bind a
  BindClose :: !Int -> ![IdInt] -> !a -> Bind a

-- create a binding by "abstracting a variable"
bind :: Exp -> Bind Exp
bind = Bind
{-# INLINEABLE bind #-}

unbind :: Bind Exp -> Exp
unbind (Bind a) = a
unbind (BindOpen k ss a) =
  multi_open_exp_wrt_exp_rec k ss a
unbind (BindClose k vs a) =
  multi_close_exp_wrt_exp_rec k vs a
{-# INLINEABLE unbind #-}

instance (Eq Exp) => Eq (Bind Exp) where
  b1 == b2 = unbind b1 == unbind b2

-- Exp Z is  locally closed terms
data Exp where
  Var_b :: !Int -> Exp
  Var_f :: !IdInt -> Exp
  Abs :: !(Bind Exp) -> Exp
  App :: !(Exp) -> !(Exp) -> Exp
  deriving (Generic)

-- keep track of the opening that has been done already
-- via bound-variable substitution
-- a substitution looks like
-- k=1    0 -> 0 , 1 -> 1 , k+1 -> x, k+2 -> y, ...
-- as we apply it underneath a binding, it needs to be converted to
-- a larger scope (where the newly bound variables are left alone).
-- k=2    0 -> 0 , 1 -> 1 , 2 -> 2, k+1 -> x, k+2 -> y, ...
-- more generally, we have the scope depth k and a n-ary mapping for variables k+i for 0<=i<n

multi_open_exp_wrt_exp_rec :: Int -> [Exp] -> Exp -> Exp
multi_open_exp_wrt_exp_rec k vn e =
  case e of
    Var_b i -> openIdx i k vn
    Var_f x -> Var_f x
    Abs (BindOpen nk1 vm b) -> Abs (BindOpen (k + nk1) (vm <> vn) b)
    Abs b ->
      Abs (BindOpen (k + 1) vn (unbind b))
    (App e1 e2) ->
      App
        (multi_open_exp_wrt_exp_rec k vn e1)
        (multi_open_exp_wrt_exp_rec k vn e2)

-- when we find a bound variable, determine whether we should
-- leave it alone or replace it
openIdx :: Int -> Int -> [Exp] -> Exp
openIdx i j v
  | i >= j = v !! (i - j)
  | otherwise = Var_b 0
{-# INLINEABLE openIdx #-}

open :: Bind Exp -> Exp -> Exp
open (BindOpen k vs e) u = multi_open_exp_wrt_exp_rec 0 (u : vs) e
open b u = multi_open_exp_wrt_exp_rec 0 [u] (unbind b)
{-# INLINEABLE open #-}

-----------------------------------------------------------------

-- Create `n` new "bound" variables by looking for the "free" variables in the vector
-- and replacing them with the appropriate indices
-- `k` is the current nesting level. Once we are done, it will be k+n.
--    example:  say k=1, n=2 and vec = {x,y}
--       x y 0 (\. x y 1 0 w)  ==>  1 2 0 (\. 2 3 1 0 w)
--                                  0+k 1+k 0 (\. 0+k+1 1+k+1 1 0
multi_close_exp_wrt_exp_rec :: Int -> [IdInt] -> Exp -> Exp
multi_close_exp_wrt_exp_rec k xs e =
  case e of
    Var_f x -> case elemIndex x xs of
      Just n -> Var_b (n + k)
      Nothing -> Var_f x
    Var_b n2 -> Var_b n2
    Abs (BindClose k0 ys a) ->
      Abs (BindClose k0 (ys <> xs) a)
    Abs b -> Abs (bind recur)
      where
        recur = multi_close_exp_wrt_exp_rec (k + 1) xs (unbind b)
    App e2 e3 ->
      App
        (multi_close_exp_wrt_exp_rec k xs e2)
        (multi_close_exp_wrt_exp_rec k xs e3)

close :: IdInt -> Exp -> Bind Exp
close x e = BindClose 0 [x] e
{-# INLINEABLE close #-}

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNamelessV3",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

{- ------------------------------------------ -}

toDB :: LC.LC IdInt -> Exp
toDB = to 0 []
  where
    to :: Int -> [(IdInt, Int)] -> LC.LC IdInt -> Exp
    to k vs (LC.Var v@(IdInt i)) = maybe (Var_f v) Var_b (lookup v vs)
    to k vs (LC.Lam x b) = Abs (bind b')
      where
        b' = to (k + 1) ((x, 0) : mapSnd (1 +) vs) b
    to k vs (LC.App f a) = App (to k vs f) (to k vs a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

fromDB :: Exp -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp -> LC.LC IdInt
    from n (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | i < 0 = LC.Var (IdInt $ i)
      | i >= n = LC.Var (IdInt $ i)
      | otherwise = LC.Var (IdInt (n - i -1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)

aeq :: Exp -> Exp -> Bool
aeq (Var_b i) (Var_b j) = i == j
aeq (Var_f i) (Var_f j) = i == j
aeq (Abs a) (Abs b) = aeq (unbind a) (unbind b)
aeq (App a b) (App c d) = aeq a c && aeq b d

instance NFData Exp where
  rnf (Var_b i) = rnf i
  rnf (Var_f i) = rnf i
  rnf (Abs b) = rnf b
  rnf (App a b) = rnf a `seq` rnf b

-- free variable substitution
subst :: Exp -> IdInt -> Exp -> Exp
subst u y e = subst0 e
  where
    subst0 :: Exp -> Exp
    subst0 e = case e of
      (Var_b n) -> Var_b n
      (Var_f x) -> (if x == y then u else (Var_f x))
      (Abs b) -> Abs (bind (subst0 (unbind b)))
      (App e1 e2) -> App (subst0 e1) (subst0 e2)

fv :: Exp -> Set IdInt
fv e =
  case e of
    (Var_b nat) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs b) -> fv (unbind b)
    (App e1 e2) -> fv e1 `Set.union` fv e2

{- --------------------------------------- -}

type N a = State IdInt a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfd :: Exp -> Exp
nfd e = State.evalState (nf' e) firstBoundId

nf' :: Exp -> N Exp
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
whnf :: Exp -> N Exp
whnf e@(Var_f _) = return e
whnf e@(Var_b _) = error "BUG"
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (open b a)
    _ -> return $ App f' a

-- Fueled version

nfi :: Int -> Exp -> Maybe Exp
nfi n e = State.evalStateT (nfi' n e) firstBoundId

type NM a = State.StateT IdInt Maybe a

nfi' :: Int -> Exp -> NM Exp
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
whnfi :: Int -> Exp -> NM Exp
whnfi 0 _ = State.lift Nothing
whnfi n e@(Var_f _) = return e
whnfi n e@(Var_b _) = error "BUG"
whnfi n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> whnfi (n -1) (open b a)
    _ -> return $ App f' a