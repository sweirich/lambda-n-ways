{-
This version is an adaptation of Lennart's Debruijn implementation.
Instead of adjusting the indices of variables at each occurrence of the term,
it lifts the substitution as it goes under each binder.

This version is a variant of the 'Lift' implementation found in the Cornell lecture notes:
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf

It separates substitution from instantiation.
-}

module DeBruijn.Lazy.Cornell (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Lazy.Cornell",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data DB
  = DVar Int
  | DLam DB
  | DApp DB DB
  deriving (Eq)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------

nfd :: DB -> DB
nfd e@(DVar _) = e
nfd (DLam e) = DLam (nfd e)
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate b a)
    f' -> DApp (nfd f') (nfd a)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

----------------------------------------------------------

nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a

----------------------------------------------------------

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
    to vs (Lam x b) = DLam (to (x : vs) b)
    to vs (App f a) = DApp (to vs f) (to vs a)

fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)

----------------------------------------------------------

instantiate :: DB -> DB -> DB
instantiate b a = shift (-1) (subst (sub (shift 1 a)) b)
{-# INLINE instantiate #-}

{- When we are going to be adjusting the terms in the substitution,
it is important to do that *lazily*. We don't want to adjust terms that
weren't actually used in the expression. This means that it makes sense to
include a thunk in our substitution. -}

data Sub = Sub {-# UNPACK #-} !Int DB

sub :: DB -> Sub
sub a = Sub 0 a
{-# INLINE sub #-}

subst :: Sub -> DB -> DB
subst s (DVar i) = apply s i
subst s (DLam e) = DLam (subst (lift s) e)
subst s (DApp f a) = DApp (subst s f) (subst s a)

adjust :: Int -> DB -> Int -> DB
adjust o e@(DVar j) n
  | j >= n = DVar (j + o)
  | otherwise = e
adjust o (DLam e) n = DLam (adjust o e (n + 1))
adjust o (DApp f a) n = DApp (adjust o f n) (adjust o a n)

shift :: Int -> DB -> DB
shift n x = adjust n x 0
{-# INLINE shift #-}

lift :: Sub -> Sub
lift (Sub o b) = Sub (o + 1) (shift 1 b)
{-# INLINE lift #-}

apply :: Sub -> Int -> DB
apply (Sub o a) i
  | i == o = a
  | otherwise = DVar i
{-# INLINE apply #-}
