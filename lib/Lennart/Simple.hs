{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Simple module implements the Normal Form function by
-- using a na\"{i}ve version of substitution. In otherwords, this version
-- alpha-renames bound variables during substitution if they would ever
-- capture a free variable.
-- It is based on Lennart Augustsson's version from "lambda-calculus cooked four ways"
-- But uses Data.IntSet instead [Int] for variable sets
-- Also fixes a bug in selecting free variables for renaming.
-- Lennart's version only avoid variables in original term b. But we also need to
-- avoid all newly generated variables (and the variable that we are substituting for).
module Lennart.Simple (impl) where

import Control.Monad.Except
import qualified Control.Monad.State as State
import Data.List (intersperse, union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S
import Util.IdInt (IdInt, newId)
import Util.Impl (LambdaImpl (..))
import Util.Imports
import Util.Lambda
import qualified Util.Stats as Stats

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Lennart.Simple",
      impl_fromLC = id,
      impl_toLC = id,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = Util.Lambda.aeq
    }

--- No extra syntax, just uses LC IdInt

subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
subst x a = sub
  where
    sub :: LC IdInt -> LC IdInt
    sub b@(Var v)
      | v == x = a
      | otherwise = b
    sub b@(Lam v e')
      | v == x = b
      | v `elem` fvs = Lam v' (sub e'')
      | otherwise = Lam v (sub e')
      where
        v' = newId (fvs `S.union` allVars b)
        e'' = subst v (Var v') e'
    sub (App f g) = App (sub f) (sub g)

    fvs = freeVars a `S.union` (S.singleton x)

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

nf :: LC IdInt -> LC IdInt
nf e@(Var _) = e
nf (Lam x e) = Lam x (nf e)
nf (App f a) =
  case whnf f of
    Lam x b -> nf (subst x a b)
    f' -> App (nf f') (nf a)

-- Compute the weak head normal form.  It is similar to computing the normal form,
-- but it does not reduce under $\lambda$, nor does it touch an application
-- that is not a $\beta$-redex.

whnf :: LC IdInt -> LC IdInt
whnf e@(Var _) = e
whnf e@(Lam _ _) = e
whnf (App f a) =
  case whnf f of
    Lam x b -> whnf (subst x a b)
    f' -> App f' a

-- For testing, we can add a "fueled" version that also counts the number of substitutions

nfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam x e) = Lam x <$> nfi (n -1) e
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> nfi (n -1) (subst x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _ _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> whnfi (n - 1) (subst x a b)
    _ -> return $ App f' a
