-- | This module uses nominal logic
module Named.Nominal (impl) where

import qualified Named.SimpleB
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
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Nominal",
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

-- A class of types that can calculate free variables and
-- substitute.

class FreeVars e where
  freeVars :: e -> VarSet

class Subst a e where
  subst :: Sub a -> e -> e

class Var e where
  var :: IdInt -> e

-------------------------------------------------------------------

-- In this implementation we cache substitutions and fv sets at binders. That
-- means that we don't need to recalculate them and that we can combine
-- substitutions together.

data Bind e = Bind
  { bind_subst :: !(Sub e),
    bind_fvs :: !(VarSet),
    bind_var :: !IdInt,
    bind_body :: !e
  }

{-

Invariants:

1. bind_fvs is cached freeVars of e, minus v. It does not include fvs in the bind_subst.

2. The domain of the bind_subst is a subset of bind_fvs

3. The freeVars of the bind_subst do not include v (i.e. they will not capture).
   (If this would happen when constructing a bind, we will freshen v to v'
   and extend the substitution with v -> v', in the case that v is free in e.)
-}

validBind :: (FreeVars e) => Bind e -> Bool
validBind b@Bind {} =
  bind_fvs b == S.delete (bind_var b) (freeVars (bind_body b))
    && M.keysSet (bind_subst b) `S.isSubsetOf` bind_fvs b
    && bind_var b `S.notMember` freeVars (bind_subst b)

bind :: FreeVars e => IdInt -> e -> Bind e
bind v a = Bind emptySub (S.delete v (freeVars a)) v a
{-# INLINEABLE bind #-}

bindHelper :: (Var e, FreeVars e) => Sub e -> IdInt -> e -> Bind e
bindHelper s x a
  | M.null s = Bind emptySub fv x a
  | x `S.member` fv_s = Bind (M.insert x (var y) s') fv y a
  where
    fv = S.delete x (freeVars a)
    s' = M.restrictKeys s fv
    fv_s = freeVars s'
    y = maximum (fmap varSetMax [fv, fv_s])
{-# INLINEABLE bindHelper #-}

unbind :: Subst e e => Bind e -> (IdInt, e)
unbind (Bind s _fv x a) = (x, subst s a)
{-# INLINEABLE unbind #-}

instantiate :: (Show e, Subst e e) => Bind e -> e -> e
instantiate (Bind s _fv x a) b =
  subst (singleSub x b) (subst s a)
{-# INLINEABLE instantiate #-}

varSetMax :: VarSet -> IdInt
varSetMax s = maybe (toEnum 0) succ (lookupMax s)
{-# INLINEABLE varSetMax #-}

instance (FreeVars e) => FreeVars (Bind e) where
  freeVars (Bind s fv _ _) = freeVars s <> (fv S.\\ M.keysSet s)
  {-# INLINEABLE freeVars #-}

instance (Var e, FreeVars e, Subst e e, Show e) => Subst e (Bind e) where
  subst s2 b@(Bind s1 fv x e)
    -- if the substitution is empty, nothing to do
    | M.null s2 = b
    -- if the bound variable is in the domain of the substitution, we can stop.
    ---- | M.member x s2 = subst (M.delete x s2) b
    -- alpha-vary if we are in danger of capture
    {-    | x `S.member` fv_s = Bind (M.insert x (var y) s') fv' y a'
        | otherwise = Bind s' fv' x a'
        where
          a' = subst s1 e
          fv' = freeVars a'
          s' = M.restrictKeys s2 fv'
          fv_s = freeVars s'
          y = maximum (fmap varSetMax [fv', fv_s])
    -}
    -- if we could capture, alpha-vary
    | x `S.member` fv2 =
      let y = maximum (fmap varSetMax [fvb, fv2, M.keysSet s1, M.keysSet s2])
          s = M.insert x (var y) s1s2'
          s' = M.restrictKeys s (fv `S.union` S.singleton x)
       in Bind s' fv y e
    -- just compose the substitutions
    | otherwise = Bind s1s2' fv x e
    where
      fvb = freeVars b
      s2' = M.restrictKeys s2 fvb
      s1s2 = s1 `comp` s2'
      fv2 = freeVars s2'
      s1s2' = M.restrictKeys s1s2 fv

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

-- comp s1 s2 = subst s2 (subst s1 a
comp :: (Subst e e) => Sub e -> Sub e -> Sub e
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s1 if there is also a definition in s2
  | otherwise = subst s2 s1 <> s2
{-# INLINEABLE comp #-}

instance FreeVars e => FreeVars (Sub e) where
  freeVars = foldMap freeVars

instance Subst a e => Subst a (Sub e) where
  subst s2 s1 = fmap (subst s2) s1

-------------------------------------------------------------------

instance FreeVars IdInt where
  freeVars = S.singleton

-------------------------------------------------------------------

data Exp = Var !IdInt | Lam !(Bind Exp) | App !Exp !Exp

instance NFData Exp where
  rnf (Var i) = rnf i
  rnf (Lam d) = rnf d
  rnf (App a b) = rnf a `seq` rnf b

instance Var Exp where
  var = Var

instance FreeVars Exp where
  freeVars (Var v) = freeVars v
  freeVars (Lam b) = freeVars b
  freeVars (App f a) = freeVars f `S.union` freeVars a

instance Subst Exp Exp where
  subst s e = if M.null s then e else subst0 e
    where
      subst0 (Var x) = M.findWithDefault (Var x) x s
      subst0 (Lam b) = Lam (subst s b)
      subst0 (App f a) = App (subst0 f) (subst0 a)

-------------------------------------------------------------------

aeq :: LC.LC IdInt -> LC.LC IdInt -> Bool
aeq x y = aeqd (toExp x) (toExp y)

nf :: LC.LC IdInt -> LC.LC IdInt
nf = fromExp . nfd . toExp

-- Alpha-equivalence

aeqBind :: Bind Exp -> Bind Exp -> Bool
aeqBind (Bind s1 _f1 x1 b1) e2@(Bind s2 _f2 x2 b2)
  | x1 == x2 = aeqd (subst s1 b1) (subst s2 b2)
  | x1 `S.member` freeVars e2 = False
  | otherwise =
    aeqd
      (subst s1 b1)
      ( subst
          (s2 `comp` singleSub x2 (Var x1))
          b2
      )

aeqd :: Exp -> Exp -> Bool
aeqd (Var v1) (Var v2) = v1 == v2
aeqd (Lam e1) (Lam e2) = aeqBind e1 e2
aeqd (App a1 a2) (App b1 b2) = aeqd a1 b1 && aeqd a2 b2
aeqd _ _ = False

-- Computing the normal form proceeds as usual.

nfd :: Exp -> Exp
nfd e@(Var _) = e
nfd (Lam b) =
  b'
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

nfi :: Int -> Exp -> Stats.M Exp
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam b) = Lam . bind x <$> nfi (n -1) a where (x, a) = unbind b
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