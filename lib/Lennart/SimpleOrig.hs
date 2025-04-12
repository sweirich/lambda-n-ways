{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}

-- | The Simple module implements the Normal Form function by
-- using a na\"{i}ve version of substitution. In otherwords, this version
-- alpha-renames bound variables during substitution if they would ever
-- capture a free variable.
-- It is the version from Lennart Augustsson's "Lambda Calculus Cooked Four Ways"
module Lennart.SimpleOrig (impl) where

import Control.Monad.Except
import qualified Control.Monad.State as State
import Data.List (intersperse, union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S
import Util.IdInt (IdInt, firstBoundId)
import Util.Impl (LambdaImpl (..))
import Util.Imports
--- No extra syntax, just uses LC IdInt
import qualified Util.Stats as Stats
import Util.Syntax.Lambda hiding (allVars, freeVars)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Lennart.SimpleOrig",
      impl_fromLC = id,
      impl_toLC = id,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = Util.Syntax.Lambda.aeq,
      impl_eval = whnf
    }

freeVars :: (Eq v) => LC v -> [v]
freeVars (Var v) = [v]
freeVars (Lam v e) = freeVars e \\ [v]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Bool b) = []
freeVars (If a b1 b2) =
  freeVars a <> freeVars b1 <> freeVars b2

-- Compute all variables in an expression.

allVars :: (Eq v) => LC v -> [v]
allVars (Var v) = [v]
allVars (Lam _ e) = allVars e
allVars (App f a) = allVars f `union` allVars a
allVars (Bool b) = []
allVars (If a b1 b2) =
  allVars a <> allVars b1 <> allVars b2

-- NOTE: Lennart's original version had a bug.
-- it chose the new variable avoiding free variables of s + all of the variables
-- in the original term b.  However, this doesn't avoid any *new*
-- binding variables that are introduced into b to avoid capture. Nor does
-- it include x!

newId :: [IdInt] -> IdInt
newId vs = case ([firstBoundId ..] \\ vs) of (x:_) -> x ; [] -> error "BUG"

{-
subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
subst x s b = sub b
  where
    sub e@(Var v)
      | v == x = s
      | otherwise = e
    sub e@(Lam v e')
      | v == x = e
      | v `elem` fvs = Lam v' (sub e'')
      | otherwise = Lam v (sub e')
      where
        v' = newId (vs `union` freeVars e')
        e'' = subst v (Var v') e'
    sub (App f a) = App (sub f) (sub a)
    fvs = freeVars s
    vs = (x : fvs)
-}

subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
subst x s b = sub ((x : freeVars s) `union` freeVars b) x s b
  where
    sub vs x s e@(Var v)
      | v == x = s
      | otherwise = e
    sub vs x s e@(Lam v e')
      | v == x = e
      | v `elem` freeVars s =
        let v' = newId vs
            vs' = (v' : vs)
            e'' = sub vs' v (Var v') e'
         in Lam v' (sub vs' x s e'')
      | otherwise = Lam v (sub (v : vs) x s e')
    sub vs x s (App f a) = App (sub vs x s f) (sub vs x s a)
    sub vs x s (Bool b) = Bool b
    sub vs x s (If a b c) = If (sub vs x s a) (sub vs x s b) (sub vs x s c)
{-
-- important to only rename when capture could occur. this version
-- is correct, but much slower
subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
subst x s b = sub ((x : freeVars s) `union` freeVars b) x s b
  where
    sub vs x s e@(Var v)
      | v == x = s
      | otherwise = e
    sub vs x s e@(Lam v e')
      | v == x = e
      | otherwise =
        let v' = newId vs
            vs' = (v : v' : vs)
            e'' = sub vs' v (Var v') e'
         in Lam v' (sub vs' x s e'')
    sub vs x s (App f a) = App (sub vs x s f) (sub vs x s a)
-}

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
nf (Bool b) = Bool b
nf (If a b c) = case whnf a of 
    Bool True -> nf b
    Bool False -> nf c
    a' -> If (nf a') (nf b) (nf c)

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
whnf e@(Bool _) = e
whnf (If a b c) = 
  case whnf a of 
    Bool True -> whnf b
    Bool False -> whnf c
    a' -> If a' b c

-- For testing, we can add a "fueled" version that also counts the number of substitutions

nfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam x e) = Lam x <$> nfi (n -1) e
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> nfi (n -1) (subst x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a
nfi _ (Bool b) = return $ Bool b
nfi n (If a b c) = case whnf a of 
    Bool True -> nfi (n - 1) b
    Bool False -> nfi (n - 1) c
    a' -> If <$> (nfi (n-1) a') <*> (nfi (n-1) b) <*> (nfi (n-1) c)

whnfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _ _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> whnfi (n - 1) (subst x a b)
    _ -> return $ App f' a
whnfi _ e@(Bool _) = return e
whnfi n (If a b c) = 
  case whnf a of 
    Bool True -> whnfi (n - 1) b
    Bool False -> whnfi (n - 1) c
    a' -> return $ If a' b c