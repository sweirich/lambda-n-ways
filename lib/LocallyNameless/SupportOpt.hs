-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- uses Support.SubstOp library
module LocallyNameless.SupportOpt (impl, substFv, fv) where

import qualified Control.Monad.State as State
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import Debug.Trace
import GHC.Stack
import Support.SubstOpt
import Util.IdInt (IdInt (..), firstBoundId)
import qualified Util.IdInt.Set as Set
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.SupportOpt",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data Exp where
  Var :: !Var -> Exp
  Abs :: !(Bind Exp) -> Exp
  App :: !Exp -> !Exp -> Exp
  deriving (Generic, Eq, Show)

instance NFData Exp

-- NOTE: this does not preserve local closure as it traverses the term
pretty :: Exp -> String
pretty (Var x) = prettyVar x
pretty (App a1 a2) = "(App " ++ pretty a1 ++ " " ++ pretty a2 ++ ")"
pretty (Abs b) = "(Abs " ++ pretty (unbind b) ++ ")"

-------------------------------------------------------------------

-- free variable substitution
{-
substFv :: Exp -> IdInt -> Exp -> Exp
substFv u y e =
  subst0 e
  where
    subst0 :: Exp -> Exp
    subst0 e0 = case e0 of
      (Var v) -> substFvVar u y v
      (Abs b) -> Abs (bind (subst0 (unbind b)))
      (App e1 e2) -> App (subst0 e1) (subst0 e2)
-}

instance VarC Exp where
  var = Var

instance AlphaC Exp where
  fv e =
    case e of
      (Var v) -> fv v
      (Abs b) -> fv b
      (App e1 e2) -> fv e1 `Set.union` fv e2

  multi_open_rec k vn e =
    case e of
      Var v -> Var (multi_open_rec k vn v)
      Abs b -> Abs (multi_open_rec k vn b)
      App e1 e2 ->
        App (multi_open_rec k vn e1) (multi_open_rec k vn e2)

  multi_close_rec :: HasCallStack => Int -> [IdInt] -> Exp -> Exp
  multi_close_rec k xs e =
    case e of
      Var v -> Var (multi_close_rec k xs v)
      Abs b -> Abs (multi_close_rec k xs b)
      App e2 e3 ->
        App
          (multi_close_rec k xs e2)
          (multi_close_rec k xs e3)

instance SubstC Exp Exp where
  multi_subst_bv k vn e =
    case e of
      Var v -> multiSubstBvVar k vn v
      Abs b -> Abs (multi_subst_bv k vn b)
      App e1 e2 ->
        App (multi_subst_bv k vn e1) (multi_subst_bv k vn e2)
  multi_subst_fv vn e =
    case e of
      Var v -> multiSubstFvVar vn v
      Abs b -> Abs (multi_subst_fv vn b)
      App e1 e2 ->
        App (multi_subst_fv vn e1) (multi_subst_fv vn e2)

--------------------------------------------------------------

type N a = State IdInt a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfd :: HasCallStack => Exp -> Exp
nfd e =
  State.evalState (nf' e) v
  where
    v :: IdInt
    v = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

nf' :: HasCallStack => Exp -> N Exp
nf' e@(Var _) = return e
nf' (Abs b) = do
  x <- newVar
  --b' <- nf' (instantiate b (Var (F x)))
  b' <- nf' (open b (F x))
  return $ Abs (close x b')
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Abs b -> do
      -- nf' (instantiate b a)
      y <- newVar
      let b' = open b (F y)
      nf' (substFv a y b')
    _ -> App <$> nf' f' <*> nf' a

-- Compute the weak head normal form.
whnf :: Exp -> N Exp
whnf e@(Var _) = return e
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) ->
      -- whnf (instantiate b a)
      do
        y <- newVar
        let b' = open b (F y)
        whnf (substFv a y b')
    _ -> return $ App f' a

-- Fueled version

nfi :: Int -> Exp -> Stats.M Exp
nfi n e = State.evalStateT (nfi' n e) v
  where
    v :: IdInt
    v = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

type NM a = State.StateT IdInt Stats.M a

nfi' :: Int -> Exp -> NM Exp
nfi' 0 _ = State.lift Stats.done
nfi' _n e@(Var _) = return e
nfi' n (Abs e) = do
  x <- newVar
  e' <- nfi' (n - 1) (instantiate e (Var (F x)))
  return $ Abs (close x e')
nfi' n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Abs b -> State.lift Stats.count >> nfi' (n - 1) (instantiate b a)
    _ -> App <$> nfi' (n - 1) f' <*> nfi' (n -1) a

-- Compute the weak head normal form.
whnfi :: Int -> Exp -> NM Exp
whnfi 0 _ = State.lift Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ App f' a

{- ------------------------------------------ -}

toDB :: LC.LC IdInt -> Exp
toDB = to 0 []
  where
    to :: Int -> [(IdInt, Int)] -> LC.LC IdInt -> Exp
    to _k vs (LC.Var v) =
      maybe (Var (F v)) (Var . B) (lookup v vs)
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
    from _n (Var (F v)) = LC.Var v
    from (IdInt n) (Var (B i))
      | i < 0 = LC.Var (IdInt $ i)
      | i >= n = LC.Var (IdInt $ i)
      | otherwise = LC.Var (IdInt (n - i -1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)
