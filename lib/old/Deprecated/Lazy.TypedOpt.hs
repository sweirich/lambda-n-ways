{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}

-- | Based directly on transliteration of Coq output for Ott Locally
-- Nameless Backend
-- Then with types addded, and multi substitutions
-- And caching openning substitutions at binders
-- and caching closing substitutions at binders
-- NOTE: for MANY proofs, this file uses unsafeCoerce
module LocallyNameless.Lazy.TypedOpt (impl) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import Data.Type.Equality
import qualified Unsafe.Coerce as Unsafe
import Util.IdInt
import Util.Impl
import Util.Imports hiding (S)
import Util.Nat
import qualified Util.Syntax.Lambda as LC
import Util.Vec

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
-- lennart: 3.11 ms
-- random: 0.135 ms  .1
-------------------------------------------------------------------
instance NFData a => NFData (Vec a n) where
  rnf VNil = ()
  rnf (VCons a b) = rnf a `seq` rnf b

instance NFData (Sub n k) where
  rnf (Sub n k) = rnf n `seq` rnf k

instance (forall n. NFData (a n)) => NFData (Bind a m) where
  rnf (BindOpen s a) = rnf s `seq` rnf a
  rnf (Bind a) = rnf a
  rnf (BindClose _ k v a) =
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

data Bind a k where
  Bind :: !(a ('S k)) -> Bind a k
  BindOpen :: Sub n ('S k) -> !(a (Plus n ('S k))) -> Bind a k
  BindClose ::
    ('S k :~: Plus n k0) ->
    SNat k0 ->
    Vec IdInt n ->
    !(a k0) ->
    Bind a k

-- create a binding by "abstracting a variable"
-- doesn't remember any previously opened bindings
bind :: Exp ('S k) -> Bind Exp k
bind x = Bind x
{-# INLINEABLE bind #-}

unbind :: forall k. Bind Exp k -> Exp ('S k)
unbind (Bind a) = a
unbind (BindOpen ss a) =
  multi_open_exp_wrt_exp_rec ss a
unbind (BindClose Refl k vs a) =
  multi_close_exp_wrt_exp_rec k vs a
{-# INLINEABLE unbind #-}

instance (Eq (Exp ('S n))) => Eq (Bind Exp n) where
  b1 == b2 = unbind b1 == unbind b2

-- Exp Z is  locally closed terms
data Exp (n :: Nat) where
  Var_b :: !(Idx n) -> Exp n
  Var_f :: !IdInt -> Exp n
  Abs :: !(Bind Exp n) -> Exp n
  App :: !(Exp n) -> !(Exp n) -> Exp n
  deriving (Generic)

-- instance Show (Exp n) where

-- keep track of the opening that has been done already
-- via bound-variable substitution
-- a substitution looks like
-- k=1    0 -> 0 , 1 -> 1 , k+1 -> x, k+2 -> y, ...
-- as we apply it underneath a binding, it needs to be converted to
-- a larger scope (where the newly bound variables are left alone).
-- k=2    0 -> 0 , 1 -> 1 , 2 -> 2, k+1 -> x, k+2 -> y, ...
-- more generally, we have the scope depth k and a n-ary mapping for variables k+i for 0<=i<n

data Sub n k where
  Sub :: SNat k -> Vec (Exp 'Z) n -> Sub n k

emptySub :: Sub 'Z 'Z
emptySub = Sub SZ VNil

appendSub :: Sub m k -> Sub n k -> Sub (Plus m n) k
appendSub (Sub k ss0) (Sub _ ss1) = Sub k (append ss0 ss1)

plus_S_r :: forall n k. 'S (Plus n k) :~: Plus n ('S k)
plus_S_r = Unsafe.unsafeCoerce Refl

conv_plus_S_r :: forall n k a. a ('S (Plus n k)) -> a (Plus n ('S k))
conv_plus_S_r
  | Refl <- plus_S_r @n @k = id

plus_Z_r :: forall n. Plus n 'Z :~: n
plus_Z_r = Unsafe.unsafeCoerce Refl

plus_inj :: forall n k m. Plus n ('S k) :~: 'S m -> Plus n k :~: m
plus_inj = Unsafe.unsafeCoerce Refl

multi_open_exp_wrt_exp_rec :: forall n k. Sub n k -> Exp (Plus n k) -> Exp k
multi_open_exp_wrt_exp_rec ss@(Sub (k :: SNat k) (vn :: Vec (Exp Z) n)) e =
  case e of
    Var_b (i :: Idx (Plus n k)) -> openIdx i k vn
    Var_f x -> Var_f x
    Abs
      ( BindOpen
          ( Sub
              (_ :: SNat ('S (Plus n k)))
              (vm :: Vec (Exp 'Z) m)
            )
          (b :: Exp (Plus m ('S (Plus n k))))
        ) -> Abs (BindOpen ss2 b2)
        where
          ss2 :: Sub (Plus m n) ('S k)
          ss2 = Sub (SS k) (append vm vn)
          b2 :: Exp (Plus (Plus m n) ('S k))
          b2 = Unsafe.unsafeCoerce b
    Abs b ->
      Abs (BindOpen ss2 b2)
      where
        ss2 :: Sub n (S k)
        ss2 = Sub (SS k) vn
        b2 :: Exp (Plus n (S k))
        b2 = conv_plus_S_r @n @k (unbind b)
    (App e1 e2) ->
      App
        (multi_open_exp_wrt_exp_rec ss e1)
        (multi_open_exp_wrt_exp_rec ss e2)

shiftV :: Exp k -> Exp ('S k)
shiftV (Var_b n) = Var_b (FS n)
shiftV x = Unsafe.unsafeCoerce x

-- when we find a bound variable, determine whether we should
-- leave it alone or replace it
openIdx :: forall n k. Idx (Plus n k) -> SNat k -> Vec (Exp 'Z) n -> Exp k
openIdx i SZ v
  | Refl <- plus_Z_r @n = inth i v
openIdx FZ (SS n) v = Var_b FZ
openIdx (FS (m :: Idx m0)) (SS (k :: SNat k0)) v
  | Refl <- plus_S_r @n @k0 =
    shiftV (openIdx m k v)
  where
    p1 :: S m0 :~: Plus n (S k0)
    p1 = Refl
    p2 :: S k0 :~: k
    p2 = Refl
    p3 :: S (Plus n k0) :~: Plus n (S k0)
    p3 = plus_S_r @n @k0
    p5 :: m0 :~: Plus n k0
    p5 = Unsafe.unsafeCoerce Refl

open :: Bind Exp Z -> Exp Z -> Exp Z
open
  ( BindOpen
      (Sub (k :: SNat (S Z)) (vs :: Vec (Exp Z) n))
      (e :: Exp (Plus n (S Z)))
    )
  u
    | Refl <- plus_S_r @n @Z =
      f
    where
      f = multi_open_exp_wrt_exp_rec ss e'
      ss :: Sub (S n) Z
      ss = Sub SZ (VCons u vs)
      e' :: Exp (Plus (S n) Z)
      e' = Unsafe.unsafeCoerce e
open b u = multi_open_exp_wrt_exp_rec ss (unbind b)
  where
    ss = Sub SZ (VCons u VNil)

-----------------------------------------------------------------

sPlus :: SNat n -> SNat m -> SNat (Plus n m)
sPlus SZ m = m
sPlus (SS n) m = SS (sPlus n m)

sLength :: Vec a n -> SNat n
sLength VNil = SZ
sLength (VCons _ v) = SS (sLength v)

conv :: forall n k a. a (S (Plus n k)) -> a (Plus n (S k))
conv x = case plus_S_r @n @k of Refl -> x

find :: IdInt -> Vec IdInt n -> Maybe (Idx n)
find x VNil = Nothing
find x (VCons y vs)
  | x == y = Just FZ
  | otherwise = FS <$> find x vs

-- add k to the appropriate index
shiftIdx :: forall n k. Idx n -> SNat k -> Idx (Plus n k)
shiftIdx n SZ
  | Refl <- plus_Z_r @n = n
shiftIdx n (SS (k0 :: SNat k0))
  | Refl <- plus_S_r @n @k0 = FS (shiftIdx n k0)

weakenIdxL :: forall n k. Idx k -> Idx (Plus n k)
weakenIdxL = Unsafe.unsafeCoerce

-- Create `n` new "bound" variables by looking for the "free" variables in the vector
-- and replacing them with the appropriate indices
-- `k` is the current nesting level. Once we are done, it will be k+n.
--    example:  say k=1, n=2 and vec = {x,y}
--       x y 0 (\. x y 1 0 w)  ==>  1 2 0 (\. 2 3 1 0 w)
--                                  0+k 1+k 0 (\. 0+k+1 1+k+1 1 0
multi_close_exp_wrt_exp_rec ::
  forall n k.
  SNat k ->
  Vec IdInt n ->
  Exp k ->
  Exp (Plus n k)
multi_close_exp_wrt_exp_rec k xs e =
  case e of
    Var_f x -> case find x xs of
      Just n -> Var_b (shiftIdx n k)
      Nothing -> Var_f x
    Var_b n2 -> Var_b (weakenIdxL @n n2)
    Abs
      ( BindClose
          Refl
          (k0 :: SNat k0)
          (ys :: Vec IdInt n0)
          (a :: Exp k0)
        ) ->
        Abs (BindClose pf2 k0 v a)
        where
          v :: Vec IdInt (Plus n0 n)
          v = append ys xs
          pf1 :: S k :~: Plus n0 k0
          pf1 = Refl
          pf2 :: S (Plus n k) :~: Plus (Plus n0 n) k0
          pf2 = Unsafe.unsafeCoerce Refl
    Abs b
      | Refl <- plus_S_r @n @k ->
        Abs
          (bind recur')
      where
        ub :: Exp (S k)
        ub = unbind b
        recur :: Exp (Plus n (S k))
        recur = multi_close_exp_wrt_exp_rec (SS k) xs ub
        recur' :: Exp (S (Plus n k))
        recur' = Unsafe.unsafeCoerce recur
    App e2 e3 ->
      App
        (multi_close_exp_wrt_exp_rec k xs e2)
        (multi_close_exp_wrt_exp_rec k xs e3)

close :: IdInt -> Exp Z -> Bind Exp Z
close x e =
  BindClose Refl SZ (VCons x VNil) e

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.Lazy.TypedOpt",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

{- ------------------------------------------ -}

toDB :: LC.LC IdInt -> Exp Z
toDB = to SZ []
  where
    to :: SNat n -> [(IdInt, Idx n)] -> LC.LC IdInt -> Exp n
    to k vs (LC.Var v@(IdInt i)) = maybe (Var_f v) Var_b (lookup v vs)
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
    from n (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | toInt i < 0 = LC.Var (IdInt $ toInt i)
      | toInt i >= n = LC.Var (IdInt $ toInt i)
      | otherwise = LC.Var (IdInt (n - (toInt i) -1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)

aeq :: Exp n -> Exp n -> Bool
aeq (Var_b i) (Var_b j) = i == j
aeq (Var_f i) (Var_f j) = i == j
aeq (Abs a) (Abs b) = aeq (unbind a) (unbind b)
aeq (App a b) (App c d) = aeq a c && aeq b d

instance NFData (Exp n) where
  rnf (Var_b i) = rnf i
  rnf (Var_f i) = rnf i
  rnf (Abs b) = rnf b
  rnf (App a b) = rnf a `seq` rnf b

-- no bound variables to weaken.
weaken :: forall m n. Exp n -> Exp (Plus n m)
weaken = Unsafe.unsafeCoerce

-- free variable substitution
subst :: Exp Z -> IdInt -> Exp Z -> Exp Z
subst u y e = subst0 SZ e
  where
    subst0 :: forall n. SNat n -> Exp n -> Exp n
    subst0 k e = case e of
      (Var_b n) -> Var_b n
      (Var_f x) -> (if x == y then weaken @n u else (Var_f x))
      (Abs b) -> Abs (bind (subst0 (SS k) (unbind b)))
      (App e1 e2) -> App (subst0 @n k e1) (subst0 @n k e2)

fv :: Exp n -> Set IdInt
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

nfd :: Exp Z -> Exp Z
nfd e = State.evalState (nf' e) firstBoundId

nf' :: Exp Z -> N (Exp Z)
nf' e@(Var_f _) = return e
--nf' e@(Var_b _) = error "should not reach this"
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
--whnf e@(Var_b _) = error "BUG"
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (open b a)
    _ -> return $ App f' a

-- Fueled version

nfi :: Int -> Exp Z -> Maybe (Exp Z)
nfi n e = State.evalStateT (nfi' n e) firstBoundId

type NM a = State.StateT IdInt Stats.M a

nfi' :: Int -> (Exp Z) -> NM (Exp Z)
nfi' 0 _ = State.lift Stats.done
nfi' n e@(Var_f _) = return e
--nfi' n e@(Var_b _) = error "should not reach this"
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
whnfi :: Int -> Exp Z -> NM (Exp Z)
whnfi 0 _ = State.lift Stats.done
whnfi n e@(Var_f _) = return e
--whnfi n e@(Var_b _) = error "BUG"
whnfi n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (open b a)
    _ -> return $ App f' a