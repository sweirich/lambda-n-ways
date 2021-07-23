-- | This module is trying to make a "delayed" substitution version
-- of the "Simple" implementation.
-- Strangely, composing substitutions too much causes this impl to really slow
-- down on the lennart/nf benchmark.
module Named.SimpleH (impl) where

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
import qualified Util.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.SimpleH",
      impl_fromLC = toExp,
      impl_toLC = fromExp,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = aeqd
    }

type VarSet = S.IdIntSet

lookupMax :: VarSet -> Maybe IdInt
lookupMax vs = if S.null vs then Nothing else Just $ S.findMax vs

-- Get a variable which is not in the given set.

newId :: VarSet -> IdInt
newId vs = case lookupMax vs of
  Just v -> succ v
  Nothing -> toEnum 0

-------------------------------------------------------------------

-- In this implementation we cache substitutions and fv sets at binders.
-- That means that we can combine substitutions together.
-- NOTE: the cached substitution *has not* been applied to the binder.
-- so this means that we haven't yet done any renaming of the binder (to avoid capture)
-- or pruning of the substitution (to cut off substitution early).
data Bind e = Bind
  { bind_subst :: !(Sub e),
    bind_fvs :: !(VarSet),
    bind_var :: !IdInt,
    bind_body :: !e
  }

{-

Invariants:

1. bind_fvs is cached freeVars of e, minus v

3. The domain of the bind_subst is a subset of bind_fvs

3. The freeVars of the bind_subst do not include v (i.e. they will not capture).
   (If this would happen when constructing a bind, we will freshen v to v'
   and extend the substitution with v -> v', in the case that v is free in e.)
-}

validBind :: Bind Exp -> Bool
validBind b@Bind {} =
  bind_fvs b == S.delete (bind_var b) (freeVars (bind_body b))

bind :: IdInt -> Exp -> Bind Exp
bind v a = Bind emptySub (S.delete v (freeVars a)) v a
{-# INLINEABLE bind #-}

unbind :: Bind Exp -> (IdInt, Exp)
unbind b = (y, subst s a)
  where
    (y, s, a) = unbindHelper b
{-# INLINEABLE unbind #-}

-- | This part does the dirty work with pushing a substitution through
-- the binder. It returns but does not actually apply the substitution.
-- 1. renaming bound variable to avoid capture
-- 2. pruning the substitution to terminate early
unbindHelper :: Bind Exp -> (IdInt, Sub Exp, Exp)
unbindHelper (Bind s fv x a)
  -- fast-path
  | M.null s = (x, s, a)
  -- alpha-vary if in danger of capture
  | x `S.member` fv_s = (y, M.insert x (Var y) s', a)
  -- usual case, but prune substitution
  | otherwise = (x, s', a)
  where
    -- restrict to the free variables of the term
    s' = M.restrictKeys s fv
    fv_s = freeVarsSub s'
    y = maximum (fmap varSetMax [fv, fv_s])
{-# INLINEABLE unbindHelper #-}

instantiate :: Bind Exp -> Exp -> Exp
instantiate b u = subst (M.singleton y u) a
  where
    (y, a) = unbind b
{-
instantiate b u = subst (s `comp` (M.singleton y u)) a
  where
    (y, s, a) = unbindHelper b
    -}
{-# INLINEABLE instantiate #-}

varSetMax :: VarSet -> IdInt
varSetMax s = maybe (toEnum 0) succ (lookupMax s)
{-# INLINEABLE varSetMax #-}

freeVarsBind :: Bind Exp -> S.IdIntSet
freeVarsBind b = freeVarsSub s <> (bind_fvs b S.\\ M.keysSet s)
  where
    (x, s, a) = unbindHelper b
{-# INLINEABLE freeVarsBind #-}

substBind :: M.IdIntMap Exp -> Bind Exp -> Bind Exp
substBind s2 b@(Bind s1 _fv _x _a)
  | M.null s2 = b
  -- forcing this substitution, instead of delaying it,  seems to be particularly
  -- important for the lennart/nf benchmark. (14.0 sec -> 0.11 sec)
  | M.null s1 = bind x (subst s' a)
  where
    (x, s', a) = unbindHelper (b {bind_subst = s2})
{-
  bind y a'
  where
    s' = M.restrictKeys s2 fv
    fv_s = freeVarsSub s'
    (y, a') =
      if M.null s'
        then (x, a)
        else
          if x `S.member` fv_s
            then -- is this fresh enough? what if we pick a variable that is already
            -- in scope? as long as it doesn't appear free, it is ok to shadow it.
            -- \x. \z. ((\y. \x. y) x)  --> \x. \z. (\z. x)

              let y = maximum (fmap varSetMax [fv, fv_s])
               in let s'' = M.insert x (Var y) s'
                   in (y, subst s'' a)
            else (x, subst s2 a) -}
substBind s2 b@(Bind s1 _fv _x _e) = b {bind_subst = s2 `comp` s1}

instance (NFData a) => NFData (Bind a) where
  rnf (Bind s f x a) = rnf s `seq` rnf f `seq` rnf x `seq` rnf a

-------------------------------------------------------------------

type Sub = M.IdIntMap

emptySub :: Sub e
emptySub = M.empty
{-# INLINEABLE emptySub #-}

singleSub :: IdInt -> e -> Sub e
singleSub = M.singleton
{-# INLINEABLE singleSub #-}

comp :: Sub Exp -> Sub Exp -> Sub Exp
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = substSub s1 s2 <> s1
{-# INLINEABLE comp #-}

freeVarsSub :: M.IdIntMap Exp -> S.IdIntSet
freeVarsSub = foldMap freeVars

substSub :: Functor f => M.IdIntMap Exp -> f Exp -> f Exp
substSub s2 s1 = fmap (subst s2) s1

-------------------------------------------------------------------
-------------------------------------------------------------------

data Exp = Var !IdInt | Lam !(Bind Exp) | App !Exp !Exp

instance NFData Exp where
  rnf (Var i) = rnf i
  rnf (Lam d) = rnf d
  rnf (App a b) = rnf a `seq` rnf b

freeVars :: Exp -> S.IdIntSet
freeVars (Var v) = S.singleton v
freeVars (Lam b) = freeVarsBind b
freeVars (App f a) = freeVars f `S.union` freeVars a

subst :: M.IdIntMap Exp -> Exp -> Exp
subst s e = if M.null s then e else subst0 e
  where
    subst0 (Var x) = M.findWithDefault (Var x) x s
    subst0 (Lam b) = Lam (substBind s b)
    subst0 (App f a) = App (subst0 f) (subst0 a)

-------------------------------------------------------------------

aeq :: LC.LC IdInt -> LC.LC IdInt -> Bool
aeq x y = aeqd (toExp x) (toExp y)

nf :: LC.LC IdInt -> LC.LC IdInt
nf = fromExp . nfd . toExp

-- Alpha-equivalence

aeqBind :: Bind Exp -> Bind Exp -> Bool
aeqBind b1 b2
  | x1 == x2 -- aeqd (subst s1 a1) (subst s2 a2)
    =
    aeqd (subst s1 a1) (subst s2 a2)
  | x1 `S.member` freeVarsBind b2 = False
  | otherwise = aeqd (subst s1 a1) (subst (M.singleton x2 (Var x1) `comp` s2) a2)
  where
    (x1, s1, a1) = unbindHelper b1
    (x2, s2, a2) = unbindHelper b2

aeqd :: Exp -> Exp -> Bool
aeqd (Var v1) (Var v2) = v1 == v2
aeqd (Lam e1) (Lam e2) = aeqBind e1 e2
aeqd (App a1 a2) (App b1 b2) = aeqd a1 b1 && aeqd a2 b2
aeqd _ _ = False

-- Computing the normal form proceeds as usual.

nfd :: Exp -> Exp
nfd e@(Var _) = e
nfd (Lam b) = b'
  where
    (x, a) = unbind b
    b' = Lam (bind x (nfd a))
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

nfi :: Int -> Exp -> Maybe Exp
nfi 0 _e = Nothing
nfi _n e@(Var _) = return e
nfi n (Lam b) = Lam . bind x <$> nfi (n -1) a where (x, a) = unbind b
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> nfi (n -1) (instantiate b a)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Maybe Exp
whnfi 0 _e = Nothing
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> whnfi (n - 1) (instantiate b a)
    _ -> return $ App f' a

---------------------------------------------------------

toExp :: LC.LC IdInt -> Exp
toExp = to
  where
    to (LC.Var v) = Var v
    to (LC.Lam x b) = Lam (bind x (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

fromExp :: Exp -> LC.LC IdInt
fromExp = from
  where
    from (Var i) = LC.Var i
    from (Lam b) = LC.Lam x (from a)
      where
        (x, a) = unbind b
    from (App f a) = LC.App (from f) (from a)

---------------------------------------------------------

instance Show Exp where
  show = PP.renderStyle PP.style . ppExp 0

ppExp :: Int -> Exp -> Doc
ppExp _ (Var v) = PP.text $ show v
ppExp p (Lam b) =
  pparens (p > 0) $
    PP.text "\\" <> PP.text (show x) <> PP.text "."
      <> ppExp 0 a
  where
    (x, a) = unbind b
ppExp p (App f a) = pparens (p > 1) $ ppExp 1 f PP.<+> ppExp 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = PP.parens d
pparens False d = d

-- * use max to calculate fresh vars

{-

benchmarking nf/SimpleB
time                 522.2 ms   (497.9 ms .. 538.7 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 521.9 ms   (519.3 ms .. 525.9 ms)
std dev              3.822 ms   (768.6 μs .. 5.013 ms)
variance introduced by outliers: 19% (moderately inflated)

* use M.restrictSet

benchmarking nf/SimpleB
time                 544.4 ms   (515.5 ms .. 611.7 ms)
                     0.998 R²   (0.996 R² .. 1.000 R²)
mean                 526.0 ms   (519.5 ms .. 537.3 ms)
std dev              10.74 ms   (2.108 ms .. 13.46 ms)
variance introduced by outliers: 19% (moderately inflated)

* make components of bind strict

benchmarking nf/SimpleB
time                 482.8 ms   (468.3 ms .. 511.9 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 482.2 ms   (474.1 ms .. 487.9 ms)
std dev              8.283 ms   (3.923 ms .. 11.59 ms)
variance introduced by outliers: 19% (moderately inflated)

* specialize var type to IdInt

benchmarking nf/SimpleB
time                 252.7 ms   (249.4 ms .. 255.4 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 254.9 ms   (253.5 ms .. 256.8 ms)
std dev              1.894 ms   (1.186 ms .. 2.261 ms)
variance introduced by outliers: 16% (moderately inflated)

* Data.Set -> Data.IntSet & Data.Map -> Data.IntMap

benchmarking nf/SimpleB
time                 178.7 ms   (177.4 ms .. 181.2 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 177.4 ms   (176.6 ms .. 178.3 ms)
std dev              1.301 ms   (991.4 μs .. 1.690 ms)
variance introduced by outliers: 12% (moderately inflated)

* a few more inlining pragmas

benchmarking nf/SimpleB
time                 173.5 ms   (171.8 ms .. 175.7 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 174.6 ms   (173.9 ms .. 175.2 ms)
std dev              921.1 μs   (506.0 μs .. 1.416 ms)
variance introduced by outliers: 12% (moderately inflated)
-}