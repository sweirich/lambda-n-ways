{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS -fexpose-all-unfoldings #-}

-- | This binding library supports programming with *named* representations.
-- See lib/Named/SupportH.hs and lib/Named/SupportGH.hs for examples of its use
-- without and with generic definitions.
module Support.SubstH
  ( Var (..),
    substVar,
    type Bind,
    bind,
    unbind,
    freeVarsBind,
    substBind,
    VarSet,
    Sub,
    emptySub,
    singleSub,
    comp,
    VarC (..),
    FreeVarsC (..),
    SubstC (..),
    instantiate,
  )
where

import GHC.Generics
import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Imports (NFData (..))

-------------------------------------------

-- | Variables are just Ints internally, but we treat them as names
newtype Var = V IdInt deriving (Show, Eq, NFData, Generic)

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

-- | How do we find variable uses in the expression datatype.
-- The `var` definition must always be provided to support variable renaming during substitution.
-- The `isvar` definition is used for the generic definitions of freeVars and subst.
class VarC a where
  var :: Var -> a

  isvar :: a -> Maybe Var
  isvar _ = Nothing

class FreeVarsC a where
  freeVars :: a -> VarSet
  default freeVars :: (Generic a, GFreeVars (Rep a), VarC a) => a -> VarSet
  freeVars x =
    case (isvar x) of
      Just (V v) -> S.singleton v
      Nothing -> gfreeVars (from x)

class FreeVarsC a => SubstC b a where
  subst :: Sub b -> a -> a
  default subst :: (Generic a, GSubst b (Rep a), VarC a, a ~ b) => Sub b -> a -> a
  subst s x =
    case (isvar x) of
      Just (V i) -> M.findWithDefault x i s
      Nothing -> to $ gsubst s (from x)

-- NOTE: the default definition of subst only applies when b ~ a
-- For operations like type substitution in terms, the instance can be
-- generically created with the definition:
--    subst s x = to (gsubst s (from x))

instantiate :: (VarC a, SubstC a a) => Bind a -> a -> a
instantiate (B _ y a) u = subst (singleSub (V y) u) a

-------------------------------------------------------------------
-- sub operations

emptySub :: Sub e
emptySub = M.empty

singleSub :: Var -> e -> Sub e
singleSub (V x) = M.singleton x

comp :: SubstC a a => Sub a -> Sub a -> Sub a
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = substSub s1 s2 <> s1

freeVarsSub :: FreeVarsC a => Sub a -> S.IdIntSet
freeVarsSub = foldMap freeVars

substSub :: (Functor f, SubstC b a) => Sub b -> f a -> f a
substSub s2 s1 = fmap (subst s2) s1

--------------------------------------------------------
-- var operations

instance FreeVarsC Var where
  {-# SPECIALIZE instance FreeVarsC Var #-}
  freeVars (V v) = S.singleton v

substVar :: VarC a => Sub a -> Var -> a
substVar s v@(V i) = M.findWithDefault (var v) i s

instance SubstC b Var where
  subst _ = error "Error: should never get here"

--------------------------------------------------------
-- bind operations

bind :: (FreeVarsC a) => Var -> a -> Bind a
bind (V v) a = B (S.delete v (freeVars a)) v a

unbind :: (VarC a, SubstC a a) => Bind a -> (Var, a)
unbind (B _ x a) = (V x, a)

instance (NFData a) => NFData (Bind a) where
  rnf (B f x a) = rnf f `seq` rnf x `seq` rnf a

instance (Eq a, SubstC a a, VarC a) => Eq (Bind a) where
  b1@(B _ x1 a1) == b2@(B _ x2 a2)
    | x1 == x2 = a1 == a2
    | x1 `S.member` freeVarsBind b2 = False
    | x2 `S.member` freeVarsBind b1 = False
    | otherwise =
      a1 == subst s a2
    where
      s :: Sub a
      s = M.singleton x2 (var (V x1))

freeVarsBind :: (VarC a, SubstC a a) => Bind a -> S.IdIntSet
freeVarsBind (B fv _ _) = fv

-- Apply a substitution to a binding.
-- this function is used in the Bind instance of the SubstC class
substBind :: (VarC a, SubstC a a) => Sub a -> Bind a -> Bind a
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
unbindHelper :: (VarC a, SubstC a a) => Sub a -> Bind a -> (IdInt, Sub a, a)
unbindHelper s (B fv x a)
  | x `S.member` fv_s = (y, M.insert x (var (V y)) s', a)
  -- usual case, but prune substitution
  | otherwise = (x, s', a)
  where
    -- restrict to the free variables of the term
    s' = M.restrictKeys s fv
    fv_s = freeVarsSub s'
    y = maximum (fmap S.varSetMax [fv, fv_s])

instance (VarC b, SubstC b b) => FreeVarsC (Bind b) where
  {-# SPECIALIZE instance (VarC b, SubstC b b) => FreeVarsC (Bind b) #-}
  freeVars = freeVarsBind

instance (VarC b, SubstC b b) => SubstC b (Bind b) where
  {-# SPECIALIZE instance (VarC b, SubstC b b) => SubstC b (Bind b) #-}
  subst = substBind

-------------------------------------------------------------------
class GFreeVars f where
  gfreeVars :: f a -> VarSet

class GSubst b f where
  gsubst :: Sub b -> f a -> f a

-- Constant types
instance (SubstC b c) => GSubst b (K1 i c) where
  gsubst s (K1 c) = K1 (subst s c)

instance GSubst b U1 where
  gsubst _s U1 = U1

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1

instance GSubst b V1 where
  gsubst _s = id

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g

instance SubstC b Int where
  subst _ = id

instance SubstC b Bool where
  subst _ = id

instance SubstC b () where
  subst _ = id

instance SubstC b Char where
  subst _ = id

instance (Generic a, FreeVarsC a, GSubst b (Rep [a])) => SubstC b [a] where
  subst s x = to $ gsubst s (from x)

instance (Generic a, FreeVarsC a, GSubst b (Rep (Maybe a))) => SubstC b (Maybe a) where
  subst s x = to $ gsubst s (from x)

instance (Generic (Either a1 a2), FreeVarsC (Either a1 a2), GSubst b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  subst s x = to $ gsubst s (from x)

instance (Generic (a, b), FreeVarsC (a, b), GSubst c (Rep (a, b))) => SubstC c (a, b) where
  subst s x = to $ gsubst s (from x)

instance
  ( Generic (a, b, d),
    FreeVarsC (a, b, d),
    GSubst c (Rep (a, b, d))
  ) =>
  SubstC c (a, b, d)
  where
  subst s x = to $ gsubst s (from x)

----------------------------------------------------------------

instance (FreeVarsC c) => GFreeVars (K1 i c) where
  gfreeVars (K1 c) = (freeVars c)

instance GFreeVars U1 where
  gfreeVars U1 = S.empty

instance GFreeVars f => GFreeVars (M1 i c f) where
  gfreeVars = gfreeVars . unM1

instance GFreeVars V1 where
  gfreeVars _s = S.empty

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :*: g) where
  gfreeVars (f :*: g) = gfreeVars f `S.union` gfreeVars g

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :+: g) where
  gfreeVars (L1 f) = gfreeVars f
  gfreeVars (R1 g) = gfreeVars g

instance FreeVarsC Int where
  freeVars _ = S.empty

instance FreeVarsC Bool where
  freeVars _ = S.empty

instance FreeVarsC () where
  freeVars _ = S.empty

instance FreeVarsC Char where
  freeVars _ = S.empty

instance FreeVarsC String where
  freeVars _ = S.empty

instance (Generic a, GFreeVars (Rep [a])) => FreeVarsC [a] where
  freeVars x = gfreeVars (from x)

instance (Generic a, GFreeVars (Rep (Maybe a))) => FreeVarsC (Maybe a) where
  freeVars x = gfreeVars (from x)

instance (Generic (Either a1 a2), GFreeVars (Rep (Either a1 a2))) => FreeVarsC (Either a1 a2) where
  freeVars x = gfreeVars (from x)

instance (Generic (a, b), GFreeVars (Rep (a, b))) => FreeVarsC (a, b) where
  freeVars x = gfreeVars (from x)

instance (Generic (a, b, d), GFreeVars (Rep (a, b, d))) => FreeVarsC (a, b, d) where
  freeVars x = gfreeVars (from x)