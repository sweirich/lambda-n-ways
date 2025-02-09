-- The DeBruijn module implements the Normal Form function by
-- using de Bruijn indicies and takes advantage of the "Bound" library by Ed Kmett.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module DeBruijn.Lazy.Bound (impl) where

import Bound
import Control.DeepSeq
import Control.Monad
import Data.Functor.Classes (Eq1 (..))
import GHC.Generics hiding (from, to)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Lazy.Bound",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data DB a
  = DVar a
  | DLam (Scope () DB a)
  | DApp (DB a) (DB a)
  deriving (Functor, Foldable, Traversable, Generic)

deriving instance Eq a => (Eq (DB a))

instance Eq1 DB where
  liftEq f (DVar x) (DVar y) = f x y
  liftEq f (DLam s1) (DLam s2) = liftEq f s1 s2
  liftEq f (DApp a1 b1) (DApp a2 b2) = liftEq f a1 a2 && liftEq f b1 b2
  liftEq _ _ _ = False

instance NFData a => NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------

instance Applicative DB where
  pure = DVar
  (<*>) = ap

instance Monad DB where
  return = pure
  DVar a >>= f = f a
  DApp x y >>= f = DApp (x >>= f) (y >>= f)
  DLam x >>= f = DLam (x >>>= f)

----------------------------------------------------------

nfd :: DB a -> DB a
nfd e@(DVar _) = e
nfd (DLam e) = DLam $ toScope $ nfd $ fromScope e
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate1 a b)
    f' -> DApp (nfd f') (nfd a)

whnf :: DB a -> DB a
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate1 a b)
    f' -> DApp f' a

nfi :: Int -> DB a -> Stats.M (DB a)
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam e) = DLam <$> toScope <$> nfi n (fromScope e)
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate1 a b)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB a -> Stats.M (DB a)
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate1 a b)
    _ -> return $ DApp f' a

----------------------------------------------------------

toDB :: LC IdInt -> DB IdInt
toDB = to
  where
    to :: LC IdInt -> DB IdInt
    to (Var v) = DVar v
    to (Lam v b) = DLam (abstract1 v (to b))
    to (App f a) = DApp (to f) (to a)

fromDB :: DB IdInt -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB IdInt -> LC IdInt
    from _ (DVar v) = Var v
    from n (DLam b) = Lam n (from (succ n) (instantiate1 (DVar n) b))
    from n (DApp f a) = App (from n f) (from n a)
