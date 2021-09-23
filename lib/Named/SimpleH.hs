{-# LANGUAGE ViewPatterns #-}

-- | This module optimizes the "Simple" implementation by caching free variables
-- at binders.  The ideas in this implementation are made more general in the module
--  Support.SubstH
module Named.SimpleH (impl) where

import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports (NFData (..))
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.SimpleH",
      impl_fromLC = toExp,
      impl_toLC = fromExp,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data Exp
  = Var !Var
  | Lam !(Bind Exp)
  | App !Exp !Exp
  deriving (Eq)

instance NFData Exp where
  rnf (Var v) = rnf v
  rnf (Lam a) = rnf a
  rnf (App a b) = rnf a `seq` rnf b

-------------------------------------------------------------------

freeVars :: Exp -> S.IdIntSet
freeVars (Var v) = freeVarsVar v
freeVars (Lam b) = freeVarsBind b
freeVars (App f a) = freeVars f `S.union` freeVars a

subst :: Sub Exp -> Exp -> Exp
subst s (Var v) = substVar s v
subst s (Lam b) = Lam (substBind s b)
subst s (App f a) = App (subst s f) (subst s a)

-------------------------------------------------------------------

-- Computing the normal form proceeds as usual.

nfd :: Exp -> Exp
nfd e@(Var _) = e
nfd (Lam (unbind -> (x, a))) = Lam (bind x (nfd a))
nfd (App f a) =
  case whnf f of
    Lam b -> nfd (instantiate b a)
    f' -> App (nfd f') (nfd a)

-- Compute the weak head normal form.

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam _) = e
whnf (App f a) =
  case whnf f of
    Lam b -> whnf (instantiate b a)
    f' -> App f' a

---------------------------------------------------------

nfi :: Int -> Exp -> Stats.M Exp
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam (unbind -> (x, a))) = Lam . bind x <$> nfi (n -1) a
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Stats.M Exp
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ App f' a

---------------------------------------------------------

toExp :: LC.LC IdInt -> Exp
toExp = to
  where
    to (LC.Var v) = Var (V v)
    to (LC.Lam x b) = Lam (bind (V x) (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

fromExp :: Exp -> LC.LC IdInt
fromExp = from
  where
    from (Var (V i)) = LC.Var i
    from (Lam (unbind -> (V x, a))) = LC.Lam x (from a)
    from (App f a) = LC.App (from f) (from a)

---------------------------------------------------------
-------------------------------------------

-- | Variables are just Ints internally, but we treat them as names
newtype Var = V IdInt deriving (Show, Eq, NFData)

type VarSet = S.IdIntSet

type Sub = M.IdIntMap

-- In this implementation we cache fv sets at binders.
--
data Bind a = B
  { bind_fvs :: !(VarSet),
    bind_var :: !IdInt,
    bind_body :: !a
  }

{-
Invariant:

1. bind_fvs is the freeVars of e (bind_body), minus v  (bind_var)

-}

-------------------------------------------------------------------

-- NOTE: the default definition of subst only applies when b ~ a
-- For operations like type substitution in terms, the instance can be
-- generically created with the definition:
--    subst s x = to (gsubst s (from x))

instantiate :: Bind Exp -> Exp -> Exp
instantiate (B _ y a) u = subst (singleSub (V y) u) a

-------------------------------------------------------------------
-- sub operations

singleSub :: Var -> e -> Sub e
singleSub (V x) = M.singleton x

freeVarsSub :: Sub Exp -> S.IdIntSet
freeVarsSub = foldMap freeVars

--------------------------------------------------------
-- var operations

freeVarsVar :: Var -> S.IdIntSet
freeVarsVar (V v) = S.singleton v
{-# INLINE freeVarsVar #-}

substVar :: Sub Exp -> Var -> Exp
substVar s v@(V i) = M.findWithDefault (Var v) i s
{-# INLINE substVar #-}

--------------------------------------------------------
-- bind operations

bind :: Var -> Exp -> Bind Exp
bind (V v) a = B (S.delete v (freeVars a)) v a

unbind :: Bind Exp -> (Var, Exp)
unbind (B _ x a) = (V x, a)

instance (NFData a) => NFData (Bind a) where
  rnf (B f x a) = rnf f `seq` rnf x `seq` rnf a

instance Eq (Bind Exp) where
  b1@(B _ x1 a1) == b2@(B _ x2 a2)
    | x1 == x2 = a1 == a2
    | x1 `S.member` freeVarsBind b2 = False
    | x2 `S.member` freeVarsBind b1 = False
    | otherwise =
      a1 == subst s a2
    where
      s = M.singleton x2 (Var (V x1))

freeVarsBind :: Bind Exp -> S.IdIntSet
freeVarsBind (B fv _ _) = fv

-- Apply a substitution to a binding.
-- this function is used in the Bind instance of the SubstC class
substBind :: Sub Exp -> Bind Exp -> Bind Exp
substBind s b@(B _fv _x _a)
  -- if the substitution is empty, don't do anything
  | M.null s = b
-- Use unbindHelper to prune the substitution by the fv set,
-- and compose it with any potential renaming to avoid capture
substBind s b = bind (V x) (subst s' a)
  where
    (x, s', a) = unbindHelper s b

-- | This part does the dirty work with pushing a substitution through
-- the binder. It returns but does not actually apply the substitution.
-- This has two steps:
-- 1. (potentially) renaming bound variable to avoid capture
-- 2. pruning the substitution by the free variables to terminate early
unbindHelper :: M.IdIntMap Exp -> Bind c -> (IdInt, M.IdIntMap Exp, c)
unbindHelper s (B fv x a)
  | x `S.member` fv_s = (y, M.insert x (Var (V y)) s', a)
  -- usual case, but prune substitution
  | otherwise = (x, s', a)
  where
    -- restrict to the free variables of the term
    s' = M.restrictKeys s fv
    fv_s = freeVarsSub s'
    y = maximum (fmap S.varSetMax [fv, fv_s])
