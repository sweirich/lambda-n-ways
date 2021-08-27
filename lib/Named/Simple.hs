{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Simple module implements the Normal Form function by
-- using a na\"{i}ve version of substitution. In otherwords, this version
-- alpha-renames bound variables during substitution if they would ever
-- capture a free variable.
-- It is based on Lennart Augustsson's version from "lambda-calculus cooked four ways"
-- however applies simple optimizations:
--     strict datatype for expressions, with unpacked fields
--     sets instead of lists for free variables
--     map instead of single substitution for renaming
--     fvset tracked during substitution
module Named.Simple (nf, whnf, nfi, impl, subst) where

import Control.Monad.Except
import qualified Control.Monad.State as State
import Data.List (intersperse, union, (\\))
-- | TODO: switch to idintset/idintmap
import qualified Data.Map as M
import qualified Data.Set as S
import Util.IdInt (IdInt, newId)
import Util.Impl (LambdaImpl (..))
import Util.Imports
import qualified Util.Lambda as LC
import qualified Util.Stats as Stats

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Simple",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

data Exp = Var {-# UNPACK #-} !IdInt | Lam {-# UNPACK #-} !IdInt !Exp | App !Exp !Exp
  deriving (Eq, Generic)

instance NFData Exp

fromLC :: LC.LC IdInt -> Exp
fromLC (LC.Var v) = Var v
fromLC (LC.Lam v e) = Lam v (fromLC e)
fromLC (LC.App a b) = App (fromLC a) (fromLC b)

toLC :: Exp -> LC.LC IdInt
toLC (Var v) = LC.Var v
toLC (Lam v e) = LC.Lam v (toLC e)
toLC (App a b) = LC.App (toLC a) (toLC b)

freeVars :: Exp -> S.Set IdInt
freeVars (Var v) = S.singleton v
freeVars (Lam v e) = freeVars e S.\\ S.singleton v
freeVars (App f a) = freeVars f `S.union` freeVars a

-- Compute *all* variables in an expression.

allVars :: Exp -> S.Set IdInt
allVars (Var v) = S.singleton v
allVars (Lam _ e) = allVars e
allVars (App f a) = allVars f `S.union` allVars a

--------------------------------------------------------------------------------------

applyPermLC :: LC.Perm IdInt -> Exp -> Exp
applyPermLC m (Var x) = Var (LC.applyPerm m x)
applyPermLC m (Lam x e) = Lam (LC.applyPerm m x) (applyPermLC m e)
applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)

-- inefficient version
aeq :: Exp -> Exp -> Bool
aeq = aeqd
  where
    aeqd (Var v1) (Var v2) = v1 == v2
    aeqd (Lam v1 e1) (Lam v2 e2)
      | v1 == v2 = aeqd e1 e2
      | v1 `S.member` freeVars (Lam v2 e2) = False
      | otherwise = aeqd e1 (applyPermLC p e2)
      where
        p = (LC.extendPerm LC.emptyPerm v1 v2)
    aeqd (App a1 a2) (App b1 b2) =
      aeqd a1 b1 && aeqd a2 b2
    aeqd _ _ = False

--- No extra syntax, just uses Exp

subst :: IdInt -> Exp -> Exp -> Exp
subst x s b = sub (M.singleton x s) vs0 b
  where
    sub :: Map IdInt Exp -> S.Set IdInt -> Exp -> Exp
    sub ss _ e@(Var v)
      | v `M.member` ss = (ss M.! v)
      | otherwise = e
    sub ss vs e@(Lam v e')
      | v `M.member` ss = e
      | v `elem` fvs = Lam v' (sub ss (S.insert v' vs) e'')
      | otherwise = Lam v (sub ss (S.insert v vs) e')
      where
        v' = newId vs
        e'' = subst v (Var v') e'
    sub ss vs (App f g) = App (sub ss vs f) (sub ss vs g)

    fvs = freeVars s
    vs0 = fvs `S.union` allVars b `S.union` (S.singleton x)
{-# INLINE subst #-}

-- make sure we don't rename v' to variable we are sub'ing for

{-
The normal form is computed by repeatedly performing
substitution ($\beta$-reduction) on the leftmost redex.
Variables and abstractions are easy, but in the case of
an application we must compute the function to see if
it is an abstraction.  The function cannot be computed
with the {\tt nf} function since it could perform
non-leftmost reductions.  Instead we use the {\tt whnf}
function.
-}

nf :: Exp -> Exp
nf e@(Var _) = e
nf (Lam x e) = Lam x (nf e)
nf (App f a) =
  case whnf f of
    Lam x b -> nf (subst x a b)
    f' -> App (nf f') (nf a)

-- Compute the weak head normal form.  It is similar to computing the normal form,
-- but it does not reduce under $\lambda$, nor does it touch an application
-- that is not a $\beta$-redex.

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam _ _) = e
whnf (App f a) =
  case whnf f of
    Lam x b -> whnf (subst x a b)
    f' -> App f' a

-- For testing, we can add a "fueled" version that also counts the number of substitutions

nfi :: Int -> Exp -> Stats.M Exp
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam x e) = Lam x <$> nfi (n -1) e
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> nfi (n -1) (subst x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Stats.M Exp
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _ _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> whnfi (n - 1) (subst x a b)
    _ -> return $ App f' a
