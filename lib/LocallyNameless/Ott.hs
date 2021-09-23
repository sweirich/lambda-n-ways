-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- This is the first/simplest implementation in this series
-- 0. Ott  (Lennart)
-- 1. TypedOtt (well-scoped version of Ott)
-- 1. ParScoped  (like Par.P, but scoped)
-- 2. ParOpt  (like Par.Scoped)
-- 3. Opt, like Par.B, but cache close too. Not well-scoped
-- 4. TypedOpt, well-scoped version of Opt
module LocallyNameless.Ott (impl, substFv, fv) where

import qualified Control.Monad.State as State
import Data.List (elemIndex)
import qualified Data.Set as Set
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (from, to)
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.Ott",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data Exp
  = Var_b {-# UNPACK #-} !Int
  | Var_f {-# UNPACK #-} !IdInt
  | Abs !Exp
  | App !Exp !Exp
  deriving (Eq, Ord, Generic)

instance NFData Exp

-------------------------------------------------------------

substFv :: Exp -> IdInt -> Exp -> Exp
substFv u y e =
  case e of
    (Var_b n) -> Var_b n
    (Var_f x) -> (if x == y then u else (Var_f x))
    (Abs e1) -> Abs (substFv u y e1)
    (App e1 e2) -> App (substFv u y e1) (substFv u y e2)

fv :: Exp -> Set IdInt
fv e =
  case e of
    (Var_b _) -> Set.empty
    (Var_f x) -> Set.singleton x
    (Abs e0) -> fv e0
    (App e1 e2) -> fv e1 `Set.union` fv e2

-------------------------------------------------------------
-- This definition of open is similar to the "subst" function
-- from DeBruijn.Lennart. However, because substituted terms
-- are always locally closed, they do not need to be adjusted/lifted
-- at each occurrence

open_exp_wrt_exp_rec :: Int -> Exp -> Exp -> Exp
open_exp_wrt_exp_rec k u e0 =
  case e0 of
    (Var_b n) ->
      case compare n k of
        LT -> Var_b n
        EQ -> u
        GT -> Var_b (n - 1) -- is this dead code?
    (Var_f x) -> Var_f x
    (Abs e) -> Abs (open_exp_wrt_exp_rec (k + 1) u e)
    (App e1 e2) ->
      App
        (open_exp_wrt_exp_rec k u e1)
        (open_exp_wrt_exp_rec k u e2)

open :: Exp -> Exp -> Exp
open e u = open_exp_wrt_exp_rec 0 u e

-- n1 is the index of the newly created "bound variable".
-- It starts at 0 and is incremented in each recursive call.
-- It is *also* the current binding level, i.e. an index greater than any
-- any bound variable that appears in the term. (Assuming that close is called
-- only with locally closed terms.)
close_exp_wrt_exp_rec :: Int -> IdInt -> Exp -> Exp
close_exp_wrt_exp_rec n1 x1 e1 =
  case e1 of
    Var_f x2 -> if (x1 == x2) then (Var_b n1) else (Var_f x2)
    Var_b n2 -> Var_b n2 -- if (n2 < n1) then (Var_b n2) else (Var_b (1 + n2))
    Abs e2 -> Abs (close_exp_wrt_exp_rec (1 + n1) x1 e2)
    App e2 e3 -> App (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)

close :: IdInt -> Exp -> Exp
close x1 e1 = close_exp_wrt_exp_rec 0 x1 e1

----------------------------------------------------------------

nf :: Exp -> Exp
nf e@(Var_f _) = e
nf (Var_b _) = error "should not reach this"
nf (Abs e) =
  let x = fresh e
      b' = nf (open e (Var_f x))
   in Abs (close x b')
nf (App f a) = do
  case whnf f of
    Abs b -> nf (open b a)
    f' -> App (nf f') (nf a)

-- Compute the weak head normal form.
whnf :: Exp -> Exp
whnf e@(Var_f _) = e
whnf (Var_b _) = error "should not reach this"
whnf e@(Abs _) = e
whnf (App f a) =
  case whnf f of
    (Abs b) -> whnf (open b a)
    f' -> App f' a

-- Fueled version

nfi :: Int -> Exp -> Stats.M Exp
nfi n e = State.evalStateT (nfi' n e) v
  where
    v = fresh e

fresh :: Exp -> IdInt
fresh e = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

type NM a = State.StateT IdInt Stats.M a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfi' :: Int -> Exp -> NM Exp
nfi' 0 _ = State.lift Stats.done
nfi' _n e@(Var_f _) = return e
nfi' _n (Var_b _) = error "should not reach this"
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
whnfi :: Int -> Exp -> NM Exp
whnfi 0 _ = State.lift Stats.done
whnfi _n e@(Var_f _) = return e
whnfi _n (Var_b _) = error "should not reach this"
whnfi _n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (open b a)
    _ -> return $ App f' a

---------------------------------------------------------------

toDB :: LC.LC IdInt -> Exp
toDB = to []
  where
    to vs (LC.Var v) = maybe (Var_f v) Var_b (elemIndex v vs)
    to vs (LC.Lam x b) = Abs (to (x : vs) b)
    to vs (LC.App f a) = App (to vs f) (to vs a)

fromDB :: Exp -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from _n (Var_f v) = LC.Var v
    from (IdInt n) (Var_b i)
      | i < 0 = LC.Var (IdInt i)
      | i >= n = LC.Var (IdInt i)
      | otherwise = LC.Var (IdInt (n - i -1))
    from n (Abs b) = LC.Lam n (from (succ n) b)
    from n (App f a) = LC.App (from n f) (from n a)