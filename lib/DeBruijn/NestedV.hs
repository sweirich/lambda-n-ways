{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- Source code for Hugs 1.3c,
-- extracted from "de Bruijn notation as a nested datatype",
-- by Richard S. Bird and Ross Paterson
-- renamed and adapted to benchmark framework

module DeBruijn.NestedV (impl) where

import Control.DeepSeq
import Control.Monad
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.NestedV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==),
      impl_eval = whnf
    }

-- Section 2.  Preliminaries

type Pair a = (a, a)

mapP :: (a -> b) -> Pair a -> Pair b
mapP f (x, y) = (f x, f y)

type Triple a = (a,a,a)

mapTr :: (a -> b) -> Triple a -> Triple b
mapTr f (x, y, z) = (f x, f y, f z)

-- Section 3.  de Bruijn notation

data DB v = DVar !v | DLam !(DB (Incr v)) | DApp !(Pair (DB v)) | DBool {-# unpack #-} !Bool 
  | DIf !(Triple (DB v))

deriving instance (Eq v) => (Eq (DB v))

deriving instance (Functor DB)

instance (NFData v) => NFData (DB v) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp (a, b)) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf (a, b, c)) = rnf a `seq` rnf b `seq` rnf c

data Incr v = Zero | Succ v deriving (Eq, Functor)

instance NFData v => NFData (Incr v) where
  rnf Zero = ()
  rnf (Succ v) = rnf v

mapI :: (a -> b) -> Incr a -> Incr b
mapI _f Zero = Zero
mapI f (Succ x) = (Succ . f) x

mapT :: (a -> b) -> DB a -> DB b
mapT f (DVar x) = (DVar . f) x
mapT f (DApp p) = (DApp . mapP (mapT f)) p
mapT f (DLam t) = (DLam . mapT (mapI f)) t
mapT f (DBool x) = DBool x
mapT f (DIf t) = (DIf . mapTr (mapT f)) t 
{-
foldT ::
  (forall a. a -> n a) ->
  (forall a. Pair (n a) -> n a) ->
  (forall a. n (Incr a) -> n a) ->
  DB b ->
  n b
foldT v _a _l (DVar x) = v x
foldT v a l (DApp p) = (a . mapP (foldT v a l)) p
foldT v a l (DLam t) = (l . foldT v a l) t
-}

gfoldT ::
  (forall a. m a -> n a) ->
  (forall a. Pair (n a) -> n a) ->
  (forall a. n (Incr a) -> n a) ->
  (forall a. Incr (m a) -> m (Incr a)) ->
  DB (m b) ->
  n b
gfoldT v _a _l _k (DVar x) = v x
gfoldT v a l k (DApp p) = (a . mapP (gfoldT v a l k)) p
gfoldT v a l k (DLam t) = (l . gfoldT v a l k . mapT k) t


{-
kfoldT ::
  (a -> b) ->
  (Pair b -> b) ->
  (b -> b) ->
  (Incr a -> a) ->
  DB a ->
  b
kfoldT v _a _l _k (DVar x) = v x
kfoldT v a l k (DApp p) = (a . mapP (kfoldT v a l k)) p
kfoldT v a l k (DLam t) = (l . kfoldT v a l k . mapT k) t

showT :: DB String -> String
showT = kfoldT id showP ('L' :) showI
  where
    showP (x, y) = "(" ++ x ++ " " ++ y ++ ")"
    showI Zero = "0"
    showI (Succ x) = 'S' : x

showTC :: DB Char -> String
showTC = showT . mapT wrap
  where
    wrap x = [x]
-}

joinT :: DB (DB a) -> DB a
joinT = gfoldT id DApp DLam distT

distT :: Incr (DB a) -> DB (Incr a)
distT Zero = DVar Zero
distT (Succ x) = mapT Succ x

-- Section 4.  Abstraction and application

abstract :: Eq a => a -> DB a -> DB a
abstract x = DLam . mapT (match x)

match :: Eq a => a -> a -> Incr a
match x y = if x == y then Zero else Succ y

apply :: DB a -> DB (Incr a) -> DB a
apply t = joinT . mapT (subst t . mapI DVar)

subst :: a -> Incr a -> a
subst x Zero = x
subst _x (Succ y) = y

------------------------------

-- computing the normal form proceeds as usual.

nfd :: DB a -> DB a
nfd e@(DVar _) = e
nfd (DLam e) = DLam $ nfd e
nfd (DApp (f, a)) =
  case whnf f of
    DLam b -> nfd (apply (whnf a) b)
    f' -> DApp (nfd f', nfd a)
nfd e@(DBool _) = e
nfd (DIf (a,b,c)) = 
  case whnf a of 
    DBool True -> nfd b
    DBool False -> nfd c
    a' -> DIf (nfd a', nfd b, nfd c)

-- Compute the weak head normal form.

whnf :: DB a -> DB a
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp (f, a)) =
  case whnf f of
    DLam b -> whnf (apply (whnf a) b)
    f' -> DApp (f', a)
whnf e@(DBool _) = e
whnf (DIf (a,b,c)) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf (a', b, c)

nfi :: Int -> DB a -> Stats.M (DB a)
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp (f, a)) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (apply a b)
    _ -> DApp <$> ((,) <$> nfi n f' <*> nfi n a)

whnfi :: Int -> DB a -> Stats.M (DB a)
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp (f, a)) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> whnfi (n -1) (apply a b)
    _ -> return $ DApp (f', a)

-- Convert from LC type to DB type

toDB :: LC IdInt -> DB IdInt
toDB = to
  where
    to :: LC IdInt -> DB IdInt
    to (Var v) = DVar v
    to (Lam v b) = abstract v (to b)
    to (App f a) = DApp (to f, to a)
    to (Bool b)  = DBool b
    to (If a b c) = DIf (to a, to b, to c)

--- Convert back from deBruijn to the LC type.

fromDB :: DB IdInt -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB IdInt -> LC IdInt
    from _ (DVar v) = Var v
    from n (DLam b) = Lam n (from (succ n) (apply (DVar n) b))
    from n (DApp (f, a)) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf (a,b,c)) = If (from n a) (from n b) (from n c)