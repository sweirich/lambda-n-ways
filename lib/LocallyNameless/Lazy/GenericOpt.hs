-- | Based directly on transliteration of Coq output for Ott Locally Nameless Backend
-- Then with multi substitutions
-- And caching openning substitutions at binders
-- and caching closing substitutions at binders
-- and removing types so we can use ints instead of unary nats
-- and using support.SubstOpt classes
-- and generic programming
module LocallyNameless.Lazy.GenericOpt (impl, substFv, fv) where

import qualified Control.Monad.State as State
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
    { impl_name = "LocallyNameless.Lazy.GenericOpt",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data Exp where
  Var :: Var -> Exp
  Abs :: (Bind Exp) -> Exp
  App :: Exp -> Exp -> Exp
  deriving (Generic, Eq, Show)

instance NFData Exp

-------------------------------------------------------------------

-- free variable substitution
{-
substFv :: Exp -> IdInt -> Exp -> Exp
substFv u y = subst0
  where
    subst0 :: Exp -> Exp
    subst0 e0 = case e0 of
      (Var v) -> substFvVar u y v
      (Abs b) -> Abs (bind (subst0 (unbind b)))
      -- ALT: (Abs b) -> Abs (substBind u y b)
      -- the version w/o substBind is actually faster for some reason
      (App e1 e2) -> App (subst0 e1) (subst0 e2)
-}

instance VarC Exp where
  var = Var
  isvar (Var v) = Just v
  isvar _ = Nothing

instance AlphaC Exp

instance SubstC Exp Exp where
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

nfd :: Exp -> Exp
nfd e = State.evalState (nf' e) v
  where
    v :: IdInt
    v = succ (fromMaybe firstBoundId (Set.lookupMax (fv e)))

nf' :: Exp -> N Exp
nf' e@(Var _) = return e
nf' (Abs b) = do
  x <- newVar
  b' <- nf' (instantiate b (Var (F x)))
  return $ Abs (close x b')
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Abs b -> nf' (instantiate b a)
    _ -> App <$> nf' f' <*> nf' a

-- Compute the weak head normal form.
whnf :: Exp -> N Exp
whnf e@(Var _) = return e
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (instantiate b a)
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
    (Abs b) -> State.lift Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ App f' a

{- ------------------------------------------ -}

toDB :: LC.LC IdInt -> Exp
toDB = to 0 []
  where
    to :: Int -> [(IdInt, Int)] -> LC.LC IdInt -> Exp
    to _k vs (LC.Var v) = maybe (Var (F v)) (Var . B) (lookup v vs)
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
      | otherwise = LC.Var (IdInt (n - i - 1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)
