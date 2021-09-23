{-# LANGUAGE ConstraintKinds #-}

-- | This module is trying to make a "delayed" substitution version
-- of the "Simple" implementation.
-- Strangely, composing substitutions too much causes this impl to really slow
-- down on the lennart/nf benchmark.
-- This version puts all operations (including substitution) in freshness monad
module Named.Lazy.SimpleM (impl) where

import qualified Control.Monad.Except as E
import qualified Control.Monad.State as State
import qualified Text.PrettyPrint.HughesPJ as PP
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports
  ( Generic,
    MonadError (throwError),
    MonadState (get, put),
    NFData (..),
    State,
  )
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Lazy.SimpleM",
      impl_fromLC = toExp,
      impl_toLC = fromExp,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

data Exp
  = Var Var
  | Lam (Bind Exp)
  | App Exp Exp
  deriving (Generic)

instance NFData Exp

freeVars :: Fresh m => Exp -> m VarSet
freeVars (Var v) = return $ S.singleton v
freeVars (Lam b) = freeVarsBind b
freeVars (App f a) = (<>) <$> freeVars f <*> freeVars a

subst :: Fresh m => Sub Exp -> Exp -> m Exp
subst s e = if M.null s then return e else subst0 e
  where
    subst0 (Var x) = return $ M.findWithDefault (Var x) x s
    subst0 (Lam b) = Lam <$> substBind s b
    subst0 (App f a) = App <$> subst0 f <*> subst0 a

instantiate :: Fresh m => Bind Exp -> Exp -> m Exp
instantiate b u = do
  (y, a) <- unbind b
  subst (singleSub y u) a
{-# INLINEABLE instantiate #-}

----------------------------------------------------------
-- Freshness monad
-- Get a variable which is not in the given set.

type Fresh m = MonadState IdInt m

fresh :: (MonadState IdInt m) => m IdInt
fresh = do
  x <- get
  put (succ x)
  return x

runFresh :: State s a -> s -> a
runFresh m s = State.evalState m s

-------------------------------------------------------------------
type Var = IdInt

type VarSet = S.IdIntSet

type Sub = M.IdIntMap

-- In this implementation we cache substitutions and fv sets at binders.
-- That means that we can combine substitutions together.
-- NOTE: the cached substitution *has not* been applied to the binder.
-- so this means that we haven't yet done any renaming of the binder (to avoid capture)
-- or pruning of the substitution (to cut off substitution early).
data Bind e = Bind
  { bind_subst :: !(Sub e),
    bind_fvs :: !(VarSet),
    _bind_var :: !IdInt,
    _bind_body :: !e
  }

{-

Invariants:

1. bind_fvs is cached freeVars of e, minus v

3. The domain of the bind_subst is a subset of bind_fvs

3. The freeVars of the bind_subst do not include v (i.e. they will not capture).
   (If this would happen when constructing a bind, we will freshen v to v'
   and extend the substitution with v -> v', in the case that v is free in e.)
-}

-------------------------------------------------------------------

-------------------------------------------------------------------
-- varset operations

lookupMax :: VarSet -> Maybe IdInt
lookupMax vs = if S.null vs then Nothing else Just $ S.findMax vs
{-# INLINEABLE lookupMax #-}

varSetMax :: VarSet -> IdInt
varSetMax s = maybe (toEnum 0) succ (lookupMax s)
{-# INLINEABLE varSetMax #-}

-------------------------------------------------------------------
-- bind operations

bind :: Fresh m => IdInt -> Exp -> m (Bind Exp)
bind x a = do
  fv <- (freeVars a)
  return $ Bind emptySub (S.delete x fv) x a
{-# INLINEABLE bind #-}

unbind :: Fresh m => Bind Exp -> m (IdInt, Exp)
unbind b = do
  (y, s, a) <- unbindHelper b
  a' <- subst s a
  return (y, a')
{-# INLINEABLE unbind #-}

-- | This part does the dirty work with pushing a substitution through
-- the binder. It returns but does not actually apply the substitution.
-- 1. renaming bound variable to avoid capture
-- 2. pruning the substitution to terminate early
unbindHelper :: Fresh m => Bind Exp -> m (IdInt, Sub Exp, Exp)
unbindHelper (Bind s fv x a) =
  if M.null s
    then return (x, s, a)
    else do
      let s' = M.restrictKeys s fv
      fv_s <- freeVarsSub s'
      if x `S.member` fv_s
        then do
          y <- fresh
          return (y, M.insert x (Var y) s', a)
        else return (x, s', a)
{-# INLINEABLE unbindHelper #-}

freeVarsBind :: Fresh m => Bind Exp -> m VarSet
freeVarsBind b = do
  (_, s, _) <- unbindHelper b
  s' <- freeVarsSub s
  return $ s' <> (bind_fvs b S.\\ M.keysSet s)
{-# INLINEABLE freeVarsBind #-}

allVarsBind :: Bind Exp -> VarSet
allVarsBind (Bind s _fv x a) =
  S.singleton x <> allVars a <> allVarsSub s

allVarsSub :: Sub Exp -> VarSet
allVarsSub m = M.keysSet m <> foldMap allVars m

substBind :: Fresh m => Sub Exp -> Bind Exp -> m (Bind Exp)
substBind s2 b@(Bind s1 _fv _x _a)
  | M.null s2 = return b
  -- forcing this substitution, instead of delaying it,  seems to be particularly
  -- important for the lennart/nf benchmark. (14.0 sec -> 0.11 sec)
  | M.null s1 = do
    (x, s', a) <- unbindHelper (b {bind_subst = s2})
    a' <- subst s' a
    bind x a'
  where
substBind s2 b@(Bind s1 _fv _x _e) = do
  s <- s2 `comp` s1
  return $ b {bind_subst = s}

instance (NFData a) => NFData (Bind a) where
  rnf (Bind s f x a) = rnf s `seq` rnf f `seq` rnf x `seq` rnf a

-------------------------------------------------------------------
-- sub operations

emptySub :: Sub e
emptySub = M.empty
{-# INLINEABLE emptySub #-}

singleSub :: IdInt -> e -> Sub e
singleSub = M.singleton
{-# INLINEABLE singleSub #-}

comp :: Fresh m => Sub Exp -> Sub Exp -> m (Sub Exp)
comp s1 s2
  | M.null s1 = return s2
  | M.null s2 = return s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = (<> s1) <$> (substSub s1 s2)
{-# INLINEABLE comp #-}

freeVarsSub :: Fresh m => M.IdIntMap Exp -> m S.IdIntSet
freeVarsSub m = do
  sets <- mapM freeVars (M.elems m)
  return $ foldr ((<>)) S.empty sets
{-# INLINEABLE freeVarsSub #-}

substSub :: (Fresh m) => M.IdIntMap Exp -> Sub Exp -> m (Sub Exp)
substSub s2 s1 = mapM (subst s2) s1
{-# INLINEABLE substSub #-}

-------------------------------------------------------------------
-------------------------------------------------------------------

allVars :: Exp -> S.IdIntSet
allVars (Var v) = S.singleton v
allVars (Lam b) = allVarsBind b
allVars (App f a) = allVars f `S.union` allVars a

-------------------------------------------------------------------

-- Alpha-equivalence
aeq :: Exp -> Exp -> Bool
aeq e1 e2 = runFresh (aeqd e1 e2) (varSetMax (allVars (App e1 e2)))

aeqBind :: Fresh m => Bind Exp -> Bind Exp -> m Bool
aeqBind b1 b2 = do
  (x1, s1, a1) <- unbindHelper b1
  (x2, s2, a2) <- unbindHelper b2
  fv_b2 <- freeVarsBind b2
  case () of
    ()
      | x1 == x2 -> do
        a1' <- subst s1 a1
        a2' <- subst s2 a2
        aeqd a1' a2'
      | x1 `S.member` fv_b2 ->
        return False
      | otherwise -> do
        a1' <- subst s1 a1
        a2' <- subst (M.insert x2 (Var x1) s2) a2
        aeqd a1' a2'

aeqd :: Fresh m => Exp -> Exp -> m Bool
aeqd (Var v1) (Var v2) = return $ v1 == v2
aeqd (Lam e1) (Lam e2) = aeqBind e1 e2
aeqd (App a1 a2) (App b1 b2) = (&&) <$> aeqd a1 b1 <*> aeqd a2 b2
aeqd _ _ = return False

-----------------------------------------------------------------
-- Computing the normal form proceeds as usual.

nf :: Exp -> Exp
nf a = runFresh (nfd a) (varSetMax (allVars a))

nfd :: Fresh m => Exp -> m Exp
nfd e@(Var _) = return e
nfd (Lam b) = do
  (x, a) <- unbind b
  a' <- nfd a
  Lam <$> bind x a'
nfd (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> do
      b' <- instantiate b a
      nfd b'
    _ -> App <$> nfd f' <*> nfd a

-- Compute the weak head normal form.

whnf :: Fresh m => Exp -> m Exp
whnf e@(Var _) = return e
whnf e@(Lam _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> do
      x <- instantiate b a
      whnf x
    _ -> return $ App f' a

---------------------------------------------------------

nfi :: Int -> Exp -> Stats.M Exp
nfi k e = Stats.runF (nfdi k e) (succ (S.findMax (allVars e)))

nfdi :: Int -> Exp -> Stats.FM Exp
nfdi 0 _e = Stats.doneFM
nfdi _n e@(Var _) = return e
nfdi n (Lam b) = do
  (x, a) <- unbind b
  b' <- nfdi (n -1) a
  Lam <$> (bind x b')
nfdi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> do
      Stats.countFM
      b' <- (instantiate b a)
      nfdi (n -1) b'
    _ -> App <$> nfdi (n -1) f' <*> nfdi (n -1) a

whnfi :: Int -> Exp -> Stats.FM Exp
whnfi 0 _e = Stats.doneFM
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> do
      Stats.countFM
      b' <- (instantiate b a)
      whnfi (n - 1) b'
    _ -> return $ App f' a

---------------------------------------------------------

toExp :: LC.LC IdInt -> Exp
toExp e = runFresh (to e) (succ (maximum (LC.allVars e)))
  where
    to (LC.Var v) = return $ Var v
    to (LC.Lam x b) = do
      b' <- to b
      Lam <$> bind x b'
    to (LC.App f a) = App <$> to f <*> to a

-- Convert back from deBruijn to the LC type.

fromExp :: Exp -> LC.LC IdInt
fromExp e = runFresh (from e) (succ (S.findMax (allVars e)))
  where
    from :: Exp -> State IdInt (LC.LC IdInt)
    from (Var i) = return $ LC.Var i
    from (Lam b) = do
      (x, a) <- unbind b
      LC.Lam x <$> (from a)
    from (App f a) = LC.App <$> from f <*> from a

---------------------------------------------------------