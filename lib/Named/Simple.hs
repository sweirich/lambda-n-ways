{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Simple module implements the Normal Form function by
-- using a na\"{i}ve version of substitution. In otherwords, this version
-- alpha-renames bound variables during substitution if they would ever
-- capture a free variable.
-- It is based on Lennart Augustsson's version from "lambda-calculus cooked four ways"
module Named.Simple (nf, whnf, nfi, impl, iNf, St (..), subst, SubstStat (..), show_stats, mean) where

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
    { impl_name = "Named.Simple",
      impl_fromLC = id,
      impl_toLC = id,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = Util.Lambda.aeq
    }

--- No extra syntax, just uses LC IdInt

subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
subst x a b = sub (M.singleton x a) vs0 b
  where
    sub :: Map IdInt (LC IdInt) -> S.Set IdInt -> LC IdInt -> LC IdInt
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

    fvs = freeVars a
    vs0 = fvs `S.union` allVars b `S.union` (S.singleton x)

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
    Lam x b -> Stats.count >> nfi (n -1) (subst x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _ _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam x b -> Stats.count >> whnfi (n - 1) (subst x a b)
    _ -> return $ App f' a

-- For testing, we can add a "fueled" version. We can also count
-- the number of beta reductions

data SubstStat = SubstStat
  { subst_occ :: Int, -- number of occurrences of var we are looking for
    subst_sizeB :: Int, -- size of term we are replacing with
    subst_sizeA :: Int, -- size of term we are replacing into
    subst_capture :: Bool -- does this substitution need to avoid capture?
  }

instance Show SubstStat where
  show ss = show (subst_occ ss) ++ "," ++ show (subst_sizeB ss) ++ "," ++ show (subst_sizeA ss) ++ "," ++ show (subst_capture ss)

data St = St {substStats :: [SubstStat], tmsIn :: [LC IdInt]}

-- statistics for b { a / x }
substStat :: IdInt -> LC IdInt -> LC IdInt -> SubstStat
substStat x a b =
  SubstStat
    { subst_occ = occs x b,
      subst_sizeB = size b,
      subst_sizeA = size a,
      subst_capture = captures (S.singleton x) x a b
    }

mean :: [Int] -> Double
mean xs = fromInteger (toInteger (sum xs)) / fromInteger (toInteger (length xs))

show_stats :: [SubstStat] -> String
show_stats ss
  | length ss == 0 = "none"
  | length ss < 5 = concat (intersperse " " (map show ss))
  | otherwise =
    "summary: occs=" ++ show (mean (map subst_occ ss))
      ++ ",sizeB="
      ++ show (mean (map subst_sizeB ss))
      ++ ",sizeA="
      ++ show (mean (map subst_sizeA ss))
      ++ ",capt="
      ++ show
        ( mean
            ( map
                (\x -> if x then 1 else 0)
                (map subst_capture ss)
            )
        )

iSubst :: MonadState St m => IdInt -> LC IdInt -> LC IdInt -> m (LC IdInt)
iSubst x a b = do
  s <- get
  put (s {substStats = substStat x a b : substStats s} {tmsIn = a : tmsIn s})
  return (subst x a b)

type M a = State.StateT St (Either String) a

iNf :: Int -> LC IdInt -> Maybe (LC IdInt, St)
iNf i z = hush $ State.runStateT (nfm i z :: M (LC IdInt)) (St [] [])

hush :: Either a b -> Maybe b
hush = either (const Nothing) Just

nfm :: (MonadState St m, MonadError String m) => Int -> LC IdInt -> m (LC IdInt)
nfm 0 _e = throwError "timeout"
nfm _n e@(Var _) = return e
nfm n (Lam x e) = Lam x <$> nfm (n -1) e
nfm n (App f a) = do
  f' <- whnfm (n - 1) f
  case f' of
    Lam x b -> do
      b' <- iSubst x a b
      nfm (n -1) b'
    _ -> App <$> nfm (n -1) f' <*> nfm (n -1) a

whnfm :: (MonadState St m, MonadError String m) => Int -> LC IdInt -> m (LC IdInt)
whnfm 0 _e = throwError "timeout"
whnfm _n e@(Var _) = return e
whnfm _n e@(Lam _ _) = return e
whnfm n (App f a) = do
  f' <- whnfm (n - 1) f
  case f' of
    Lam x b -> do
      b' <- iSubst x a b
      whnfm (n - 1) b'
    _ -> return $ App f' a
