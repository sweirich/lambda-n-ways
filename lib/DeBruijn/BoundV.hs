-- The DeBruijn module implements the Normal Form function by
-- using de Bruijn indicies and takes advantage of the "Bound" library by Ed Kmett.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module DeBruijn.BoundV (impl) where

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
    { impl_name = "DeBruijn.BoundV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==),
      impl_eval = whnf
    }

data DB a
  = DVar !a
  | DLam !(Scope () DB a)
  | DApp !(DB a) !(DB a)
  | DIf !(DB a) !(DB a) !(DB a)
  | DBool {-# unpack #-} !Bool
  deriving (Functor, Foldable, Traversable)

deriving instance Eq a => (Eq (DB a))

instance Eq1 DB where
  liftEq f (DVar x) (DVar y) = f x y
  liftEq f (DLam s1) (DLam s2) = liftEq f s1 s2
  liftEq f (DApp a1 b1) (DApp a2 b2) = liftEq f a1 a2 && liftEq f b1 b2
  liftEq f (DBool b1) (DBool b2) = b1 == b2
  liftEq f (DIf t1 t2 t3) (DIf u1 u2 u3) = 
    liftEq f t1 u1 && liftEq f t2 u2 && liftEq f t3 u3
  liftEq _ _ _ = False

instance NFData a => NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c
----------------------------------------------------------

instance Applicative DB where
  pure = DVar
  (<*>) = ap

instance Monad DB where
  return = pure
  DVar a >>= f = f a
  DApp x y >>= f = DApp (x >>= f) (y >>= f)
  DLam x >>= f = DLam (x >>>= f)
  DBool b >>= f = DBool b
  DIf a b c >>= f = DIf (a >>= f) (b >>= f) (c >>= f) 
----------------------------------------------------------

nfd :: DB a -> DB a
nfd e@(DVar _) = e
nfd (DLam e) = DLam $ toScope $ nfd $ fromScope e
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate1 (whnf a) b)
    f' -> DApp (nfd f') (nfd a)
nfd e@(DBool _) = e
nfd (DIf a b c) = 
  case whnf a of 
    DBool True -> nfd b
    DBool False -> nfd c
    a' -> DIf (nfd a') (nfd b) (nfd c)

whnf :: DB a -> DB a
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate1 (whnf a) b)
    f' -> DApp f' a
whnf e@(DBool _) = e
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c

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
    to (Bool b)  = DBool b
    to (If a b c) = DIf (to a) (to b) (to c)

fromDB :: DB IdInt -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB IdInt -> LC IdInt
    from _ (DVar v) = Var v
    from n (DLam b) = Lam n (from (succ n) (instantiate1 (DVar n) b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b) (from n c)