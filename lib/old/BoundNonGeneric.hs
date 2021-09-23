-- This is a "behinf the scenes" version of Bound.
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module DeBruijn.BoundNonGeneric (impl) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans
import Data.Foldable
import Data.Functor
import Data.Functor.Classes (Eq1 (..))
import Data.Maybe
import Data.Traversable
import Util.IdInt
import Util.Impl
import Util.Syntax.Lambda

-- show Var
data Var b a
  = B b
  | F a
  deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Monad (Var b) where
  return = F
  F a >>= f = f a
  B b >>= _ = B b

-- /show

-- show Scope
newtype Scope b f a = Scope {runScope :: f (Var b (f a))}
  deriving (Functor, Foldable, Traversable)

instance Monad f => Monad (Scope b f) where
  return = Scope . return . F . return
  Scope e >>= f =
    Scope $
      e >>= \v -> case v of
        B b -> return (B b)
        F ea -> ea >>= runScope . f

instance MonadTrans (Scope b) where
  lift = Scope . return . F

-- /show

-- show Abstraction and Instantiation
abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (liftM k e)
  where
    k y = case f y of
      Just z -> B z
      Nothing -> F (return y)

instantiate :: Monad f => (b -> f a) -> Scope b f a -> f a
instantiate k e =
  runScope e >>= \v -> case v of
    B b -> k b
    F a -> a

-- /show

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Bound",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = error "nfi unimplemented for BoundDB",
      impl_aeq = (==)
    }

data DB a = DVar a | DLam (Scope () DB a) | DApp (DB a) (DB a)
  deriving (Functor, Foldable, Traversable)

instance NFData a => NFData (DB a)

deriving instance Eq a => (Eq (DB a))

instance Eq1 DB where
  liftEq f (DVar x) (DVar y) = f x y
  liftEq f (DLam s1) (DLam s2) = liftEq f s1 s2
  liftEq f (DApp a1 b1) (DApp a2 b2) = liftEq f a1 a2 && liftEq f b1 b2
  liftEq _ _ _ = False

instance Applicative DB where
  pure = DVar
  (<*>) = ap

instance Monad DB where
  return = DVar
  DVar a >>= f = f a
  DApp x y >>= f = DApp (x >>= f) (y >>= f)
  DLam x >>= f = DLam (x >>>= f)

aeq :: LC IdInt -> LC IdInt -> Bool
aeq x y = toDB x == toDB y

nf :: LC IdInt -> LC IdInt
nf = fromDB . nfd . toDB

-- Computing the normal form proceeds as usual.

nfd :: DB a -> DB a
nfd e@(DVar _) = e
nfd (DLam e) = DLam $ toScope $ nfd $ fromScope e
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate a b)
    f' -> DApp (nfd f') (nfd a)

--Compute the weak head normal form.

whnf :: DB a -> DB a
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate a b)
    f' -> DApp f' a

-- Convert from LC type to DB type

toDB :: LC IdInt -> DB IdInt
toDB = to
  where
    to :: LC IdInt -> DB IdInt
    to (Var v) = DVar v
    to (Lam v b) = DLam (abstract v (to b))
    to (App f a) = DApp (to f) (to a)

-- Convert back from deBruijn to the LC type.

fromDB :: DB IdInt -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB IdInt -> LC IdInt
    from _ (DVar v) = Var v
    from n (DLam b) = Lam n (from (succ n) (instantiate (DVar n) b))
    from n (DApp f a) = App (from n f) (from n a)
