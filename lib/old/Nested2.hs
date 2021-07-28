{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- Source code for Hugs 1.3c,
-- extracted from "de Bruijn notation as a nested datatype",
-- by Richard S. Bird and Ross Paterson
-- renamed and adapted to benchmark framework
-- This is their extended version, but it doesn't pass the test cases.
-- I don't know why

module DeBruijn.Nested2 (impl) where

import Control.DeepSeq
import Control.Monad
import Util.IdInt
import Util.Impl
import Util.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Nested2",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = error "nfi unimplemented for BoundDB",
      impl_aeq = (==)
    }

-- Section 2.  Preliminaries

type Pair a = (a, a)

mapP :: (a -> b) -> Pair a -> Pair b
mapP f (x, y) = (f x, f y)

-- Section 3.  de Bruijn notation

data Incr v = Zero | Succ v deriving (Eq, Functor)

instance NFData v => NFData (Incr v) where
  rnf Zero = ()
  rnf (Succ v) = rnf v

mapI :: (a -> b) -> Incr a -> Incr b
mapI _f Zero = Zero
mapI f (Succ x) = (Succ . f) x

match :: Eq a => a -> a -> Incr a
match x y = if x == y then Zero else Succ y

subst :: a -> Incr a -> a
subst x Zero = x
subst _x (Succ y) = y

-- Section 5.  An extension of de Bruijn's notation

data DBE a
  = VarE a
  | AppE (Pair (DBE a))
  | LamE (DBE (Incr (DBE a)))

deriving instance (Eq v) => (Eq (DBE v))

deriving instance (Functor DBE)

instance (NFData v) => NFData (DBE v) where
  rnf (VarE i) = rnf i
  rnf (LamE d) = rnf d
  rnf (AppE (a, b)) = rnf a `seq` rnf b

mapE :: (a -> b) -> DBE a -> DBE b
mapE f (VarE x) = (VarE . f) x
mapE f (AppE p) = (AppE . mapP (mapE f)) p
mapE f (LamE t) = (LamE . mapE (mapI (mapE f))) t

gfoldE ::
  (forall a. m a -> n a) ->
  (forall a. Pair (n a) -> n a) ->
  (forall a. n (Incr (n a)) -> n a) ->
  (forall a. Incr a -> m (Incr a)) ->
  DBE (m b) ->
  n b
gfoldE v _a _l _k (VarE x) = v x
gfoldE v a l k (AppE p) = (a . mapP (gfoldE v a l k)) p
gfoldE v a l k (LamE t) =
  ( l . gfoldE v a l k
      . mapE (k . mapI (gfoldE v a l k))
  )
    t

joinE :: DBE (DBE a) -> DBE a
joinE = gfoldE id AppE LamE VarE

abstractE :: Eq a => a -> DBE a -> DBE a
abstractE x = LamE . mapE (mapI VarE . match x)

applyE :: DBE a -> DBE (Incr (DBE a)) -> DBE a
applyE t = joinE . mapE (subst t)

------------------------------

-- computing the normal form proceeds as usual.

nfd :: DBE a -> DBE a
nfd e@(VarE _) = e
nfd (LamE e) = LamE $ nfd e
nfd (AppE (f, a)) =
  case whnf f of
    LamE b -> nfd (applyE a b)
    f' -> AppE (nfd f', nfd a)

whnf :: DBE a -> DBE a
whnf e@(VarE _) = e
whnf e@(LamE _) = e
whnf (AppE (f, a)) =
  case whnf f of
    LamE b -> whnf (applyE a b)
    f' -> AppE (f', a)

-- Convert from LC type to DB type

toDB :: LC IdInt -> DBE IdInt
toDB = to
  where
    to :: LC IdInt -> DBE IdInt
    to (Var v) = VarE v
    to (Lam v b) = abstractE v (to b)
    to (App f a) = AppE (to f, to a)

--- Convert back from deBruijn to the LC type.

fromDB :: DBE IdInt -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DBE IdInt -> LC IdInt
    from _ (VarE v) = Var v
    from n (LamE b) = Lam n (from (succ n) (applyE (VarE n) b))
    from n (AppE (f, a)) = App (from n f) (from n a)
