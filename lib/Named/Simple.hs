{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Simple module implements the Normal Form function by
-- using a na\"{i}ve version of substitution. In otherwords, this version
-- alpha-renames bound variables during substitution if they would ever
-- capture a free variable.
-- It is based on Lennart Augustsson's version from "lambda-calculus cooked four ways"
-- however applies simple optimizations:
--     strict datatype for Expressions, with unpacked fields
--     sets instead of lists for free variables
--     map instead of single substitution for renaming
--     fvset tracked during substitution
module Named.Simple (nf, whnf, nfi, impl, subst, aeq) where

import Control.Monad.Except
import qualified Control.Monad.State as State
import Data.List (intersperse, union, (\\))
import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports
import qualified Util.Stats as Stats
import Util.Syntax.Named

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Simple",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = aeq,
      impl_eval = whnf
    }

subst :: IdInt -> Term -> Term -> Term
subst x s b = sub (M.singleton x s) vs0 b
  where
    sub :: M.IdIntMap Term -> S.IdIntSet -> Term -> Term
    sub ss _ e@(Var v)
      | v `M.member` ss = (ss M.! v)
      | otherwise = e
    sub ss vs e@(Lam v e')
      | v `M.member` ss = e
      | v `S.member` fvs = Lam v' (sub ss (S.insert v' vs) e'')
      | otherwise = Lam v (sub ss (S.insert v vs) e')
      where
        v' = S.newIdInt vs
        e'' = subst v (Var v') e'
    sub ss vs (App f g) = App (sub ss vs f) (sub ss vs g)
    sub ss vs (Bool b) = Bool b
    sub ss vs (If a b c) = If (sub ss vs a) (sub ss vs b) (sub ss vs c)

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

nf :: Term -> Term
nf e@(Var _) = e
nf (Lam x e) = Lam x (nf e)
nf (App f a) =
  case whnf f of
    Lam x b -> nf (subst x a b)
    f' -> App (nf f') (nf a)
nf (Bool b) = Bool b
nf (If a b c) = case whnf a of 
    Bool True -> nf b
    Bool False -> nf c
    a' -> If (nf a') (nf b) (nf c)

-- Compute the weak head normal form.  It is similar to computing the normal form,
-- but it does not reduce under $\lambda$, nor does it touch an application
-- that is not a $\beta$-redex.

whnf :: Term -> Term
whnf e@(Var _) = e
whnf e@(Lam _ _) = e
whnf (App f a) =
  case whnf f of
    Lam x b -> whnf (subst x a b)
    f' -> App f' a
whnf e@(Bool _) = e
whnf (If a b c) = 
  case whnf a of 
    Bool True -> whnf b
    Bool False -> whnf c
    a' -> If a' b c

-- For testing, we can add a "fueled" version that also counts the number of substitutions

nfi :: Int -> Term -> Stats.M Term
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam x e) = Lam x <$> nfi (n -1) e
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> nfi (n -1) (subst x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a
nfi n (Bool b) = return $ Bool b
nfi n (If a b c) = do
    a' <- whnfi (n - 1) a 
    case a' of 
      Bool True -> nfi (n-1) b
      Bool False -> nfi (n-1) c
      a' -> If <$> nfi (n-1) a <*> nfi (n-1) b <*> nfi (n-1) c


whnfi :: Int -> Term -> Stats.M Term
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _ _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> whnfi (n - 1) (subst x a b)
    _ -> return $ App f' a
whnfi n (Bool b) = return $ Bool b
whnfi n (If a b c) = do
    a' <- whnfi (n - 1) a 
    case a' of 
      Bool True -> nfi (n-1) b
      Bool False -> nfi (n-1) c
      a' -> pure (If a' b c)