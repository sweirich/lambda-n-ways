-- | This module is trying to make a "delayed" substitution version
-- of the "Simple" implementation.
-- Strangely, composing substitutions too much causes this impl to really slow
-- down on the lennart/nf benchmark.
module Named.Lazy.SimpleGH (impl) where

import Support.SubstH
import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports (Generic, NFData)
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Lazy.SimpleGH",
      impl_fromLC = toExp,
      impl_toLC = fromExp,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data Exp
  = Var Var
  | Lam (Bind Exp)
  | App Exp Exp
  deriving (Generic, Eq)

instance NFData Exp

-------------------------------------------------------------------

instance VarC Exp where
  {-# SPECIALIZE instance VarC Exp #-}
  var = Var
  isvar (Var v) = Just v
  isvar _ = Nothing

instance FreeVarsC Exp where
  {-# SPECIALIZE instance FreeVarsC Exp #-}

instance SubstC Exp Exp where
  {-# SPECIALIZE instance SubstC Exp Exp #-}

-------------------------------------------------------------------

-- Computing the normal form proceeds as usual.

nfd :: Exp -> Exp
nfd e@(Var _) = e
nfd (Lam b) = b'
  where
    (x, a) = unbind b
    b' = Lam (bind x (nfd a))
nfd (App f a) =
  case whnf f of
    Lam b -> nfd (instantiate b a)
    f' -> App (nfd f') (nfd a)

-- Compute the weak head normal form.

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam _) = e
whnf (App f a) =
  case whnf f of
    Lam b -> whnf (instantiate b a)
    f' -> App f' a

---------------------------------------------------------

nfi :: Int -> Exp -> Stats.M Exp
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam b) = Lam . bind x <$> nfi (n -1) a where (x, a) = unbind b
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Stats.M Exp
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam b -> Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ App f' a

---------------------------------------------------------

toExp :: LC.LC IdInt -> Exp
toExp = to
  where
    to (LC.Var v) = Var (V v)
    to (LC.Lam x b) = Lam (bind (V x) (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

fromExp :: Exp -> LC.LC IdInt
fromExp = from
  where
    from (Var (V i)) = LC.Var i
    from (Lam b) = LC.Lam x (from a)
      where
        (V x, a) = unbind b
    from (App f a) = LC.App (from f) (from a)

---------------------------------------------------------

-- * use max to calculate fresh vars

{-

benchmarking nf/SimpleB
time                 522.2 ms   (497.9 ms .. 538.7 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 521.9 ms   (519.3 ms .. 525.9 ms)
std dev              3.822 ms   (768.6 μs .. 5.013 ms)
variance introduced by outliers: 19% (moderately inflated)

* use M.restrictSet

benchmarking nf/SimpleB
time                 544.4 ms   (515.5 ms .. 611.7 ms)
                     0.998 R²   (0.996 R² .. 1.000 R²)
mean                 526.0 ms   (519.5 ms .. 537.3 ms)
std dev              10.74 ms   (2.108 ms .. 13.46 ms)
variance introduced by outliers: 19% (moderately inflated)

* make components of bind strict

benchmarking nf/SimpleB
time                 482.8 ms   (468.3 ms .. 511.9 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 482.2 ms   (474.1 ms .. 487.9 ms)
std dev              8.283 ms   (3.923 ms .. 11.59 ms)
variance introduced by outliers: 19% (moderately inflated)

* specialize var type to IdInt

benchmarking nf/SimpleB
time                 252.7 ms   (249.4 ms .. 255.4 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 254.9 ms   (253.5 ms .. 256.8 ms)
std dev              1.894 ms   (1.186 ms .. 2.261 ms)
variance introduced by outliers: 16% (moderately inflated)

* Data.Set -> Data.IntSet & Data.Map -> Data.IntMap

benchmarking nf/SimpleB
time                 178.7 ms   (177.4 ms .. 181.2 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 177.4 ms   (176.6 ms .. 178.3 ms)
std dev              1.301 ms   (991.4 μs .. 1.690 ms)
variance introduced by outliers: 12% (moderately inflated)

* a few more inlining pragmas

benchmarking nf/SimpleB
time                 173.5 ms   (171.8 ms .. 175.7 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 174.6 ms   (173.9 ms .. 175.2 ms)
std dev              921.1 μs   (506.0 μs .. 1.416 ms)
variance introduced by outliers: 12% (moderately inflated)
-}