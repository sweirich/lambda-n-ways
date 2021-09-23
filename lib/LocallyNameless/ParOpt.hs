{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Uses typed, and optimized parallel de Bruijn substitutions
-- (i.e. SubstScoped library for bound variable subst.)
module LocallyNameless.ParOpt (impl, substFv, fv) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Set as Set
import Support.Par.SubstScoped
  ( Bind (..),
    Sub (..),
    SubstC (..),
    applyS,
    bind,
    comp,
    instantiate,
    lift,
    nil,
    single,
    substBind,
    unbind,
  )
import qualified Unsafe.Coerce as Unsafe
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports
  ( Generic,
    MonadState (get, put),
    NFData,
    Set,
    State,
    fromMaybe,
  )
import Util.Nat (Idx (..), Nat (..), Plus, cmpIdx, toInt)
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

-- 0. (Lazy.Ott) Original
-- lennart: 1.03s
-- random: 0.807 ms

-- 1. (Ott) Adding strictness annotations to the datatype definition:
-- lennart: 132 ms
-- random: 3.64 ms

-- 2. (Par) Switching to strongly-typed parallel subst for bound vars
-- lennart: 3.49s
-- random: 5.12 ms

--- 3. Suspending the bv subst, ala DB_P
-- lennart: 6.64ms
-- random: 1.53 ms

--- 4. (ParOpt) unsafeCoerce for weaken
-- lennart: 6.36ms
-- random: 1.60 ms

--- 5. use smart constructor for composition in lift
-- lennart: 4.74s (v. bad)
-- random: 13ms (v.bad)
-- regressing this change

--- 6. don't use smart constructor comp at all
-- lennart: 8.10s (v.v.bad)
-- random: 2.5ms

---- 7. regressing to use comp in substBvBind only
-- lennart: 4.61s (still bad)
-- random: 2.02ms

-- GO back to 4!!! smart constructor in substBvBind and in open

-------------------------------------------------------------------

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.ParOpt",
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
  Abs :: Bind Exp n -> Exp n
  App :: !(Exp n) -> !(Exp n) -> Exp n
  deriving (Generic)

instance NFData (Exp n)

deriving instance Eq (Exp n)

----------------------------------------------------------

-- free variable substitution
substFv :: Exp 'Z -> IdInt -> Exp 'Z -> Exp 'Z
substFv u y e = subst0 e
  where
    subst_ss :: forall m n. Sub Exp m n -> Sub Exp m n
    subst_ss (Inc k) = Inc k
    subst_ss (Cons a ss) = Cons (subst0 a) (subst_ss ss)
    subst_ss (s1 :<> s2) = subst_ss s1 :<> subst_ss s2

    subst0 :: forall n. Exp n -> Exp n
    subst0 e0 = case e0 of
      (Var_b n) -> Var_b n
      (Var_f x) -> (if x == y then weaken @n u else (Var_f x))
      (Abs (Bind s1 e1)) -> Abs (Bind (subst_ss s1) (subst0 e1))
      (App e1 e2) -> App (subst0 @n e1) (subst0 @n e2)

    -- no bound variables to weaken.
    -- NOTE: this operation is only used in subst, and not used in the nf benchmarks
    weaken :: forall m n. Exp n -> Exp (Plus n m)
    weaken = Unsafe.unsafeCoerce

fv :: Exp n -> Set IdInt
fv e =
  case e of
    (Var_b _) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs b) -> fv (unbind b)
    (App e1 e2) -> fv e1 `Set.union` fv e2

---------------------------------------------------------------

substBvBind :: SubstC a => Sub a n m -> Bind a n -> Bind a m
substBvBind s2 (Bind s1 e) = Bind (s1 `comp` s2) e
{-# INLINEABLE substBvBind #-}

open :: Bind Exp 'Z -> Exp 'Z -> Exp 'Z
open (Bind (s1 :: Sub Exp m 'Z) (e :: Exp ('S m))) u = subst s e
  where
    s :: Sub Exp ('S m) 'Z
    s = (lift s1) `comp` (single u)

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
    Abs b -> Abs (bind (close_exp_wrt_exp_rec (FS n1) x1 (unbind b)))
    -- Abs (Bind (s1 :: Sub Exp m n) (b :: Exp (S m))) -> undefined
    -- here if s1 maps Var_b n1 to Var_f x1 then we can cancel the close out.
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)

close :: IdInt -> Exp 'Z -> Bind Exp 'Z
close x e = bind (close_exp_wrt_exp_rec FZ x e)

---------------------------------------------------------------

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
nfi' _n e@(Var_f _) = return e
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
whnfi _n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (open b a)
    _ -> return $ App f' a

-----------------------------------------------------

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
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)

-----------------------------------------------------------------------

{-# SPECIALIZE applyS :: Sub Exp n m -> Idx n -> Exp m #-}

{-# SPECIALIZE nil :: Sub Exp n n #-}

{-# SPECIALIZE comp :: Sub Exp m n -> Sub Exp n p -> Sub Exp m p #-}

{-# SPECIALIZE lift :: Sub Exp n m -> Sub Exp ('S n) ('S m) #-}

{-# SPECIALIZE unbind :: Bind Exp n -> Exp ('S n) #-}

{-# SPECIALIZE instantiate :: Bind Exp n -> Exp n -> Exp n #-}

{-# SPECIALIZE substBind :: Sub Exp n m -> Bind Exp n -> Bind Exp m #-}