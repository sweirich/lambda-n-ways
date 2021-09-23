{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS -fno-warn-orphans #-}

-- | https://hackage.haskell.org/package/nom
module Named.Nom where

import Data.Generics hiding (Generic, typeOf)
import GHC.Generics
import Language.Nominal.Abs
import Language.Nominal.Binder
import Language.Nominal.Name
import Language.Nominal.Nom
import Language.Nominal.Sub
import Language.Nominal.Utilities
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import Util.Imports
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Nom (Gabbay)",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

-- | Variables are string-labelled names
type Var = Name IdInt

type Bind t = KAbs Var t

deriving instance (Data IdInt)

deriving newtype instance (Swappable IdInt)

-- | Terms of the untyped lambda-calculus
data Exp
  = -- | Variable
    Var Var
  | -- | Application
    App Exp Exp
  | -- | Lambda, using abstraction-type
    Lam (KAbs Var Exp)
  deriving (Generic, Data, Swappable) -- , Show)

instance NFData (KAtom s) where
  rnf x = length (show x) == 0 `seq` ()

instance NFData b => NFData (KName a b) where
  rnf (Name x y) = rnf x `seq` rnf y

instance (NFData n, NFData b) => NFData (KAbs n b) where
  rnf x = fmap rnf x `seq` ()

instance NFData Exp

-- | helper for building lambda-abstractions
lam :: Var -> Exp -> Exp
lam x a = Lam (x @> a)

-- | Substitution.  Capture-avoidance is automatic.
instance KSub Var Exp Exp where
  sub :: Var -> Exp -> Exp -> Exp
  sub v t = rewrite $ \case
    -- 'rewrite' comes from Scrap-Your-Boilerplate generics.  It recurses properly under the binder.
    Var v' | v' == v -> Just t -- If @Var v'@, replace with @t@ ...
    _ -> Nothing -- ... otherwise recurse.

-- | weak head normal form of a lambda-term.
whnf :: Exp -> Exp
whnf (App f a) =
  case whnf f of
    Lam b' -> whnf $ b' `conc` a
    f' -> App f' a
whnf e = e

nf :: Exp -> Exp
nf e@(Var _) = e
nf (Lam (x :@> a)) = Lam (x :@> nf a)
nf (App f a) =
  case whnf f of
    Lam b -> nf (b `conc` a)
    f' -> App (nf f') (nf a)

nfi :: Int -> Exp -> Stats.M Exp
nfi 0 _e = Stats.done
nfi _n e@(Var _) = return e
nfi n (Lam (x :@> e)) = (\t -> (Lam (x :@> t))) <$> nfi (n -1) e
nfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam (x :@> b) -> Stats.count >> nfi (n -1) (sub x a b)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Stats.M Exp
whnfi 0 _e = Stats.done
whnfi _n e@(Var _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam (x :@> b) -> Stats.count >> whnfi (n - 1) (sub x a b)
    _ -> return $ App f' a

aeq :: Exp -> Exp -> Bool
aeq = aeqd
  where
    aeqd (Var v1) (Var v2) = v1 == v2
    aeqd (Lam (y :@> b1)) (Lam (z :@> b2)) =
      if y == z
        then aeqd b1 b2
        else aeqd b1 (swpN y z b2)
    aeqd (App a1 a2) (App b1 b2) =
      aeqd a1 b1 && aeqd a2 b2
    aeqd _ _ = False

nextIdInt :: [(a, IdInt)] -> IdInt
nextIdInt [] = toEnum 0
nextIdInt ((_, y) : xs) = max (succ y) (nextIdInt xs)

getVar :: Eq a => a -> [(a, b)] -> b
getVar x xs = case lookup x xs of
  Just y -> y
  Nothing -> error "UNBOUND variable"

fromLC :: LC.LC IdInt -> Exp
fromLC = go []
  where
    go :: [(IdInt, Name IdInt)] -> LC.LC IdInt -> Exp
    go xs (LC.Var x) = Var (getVar x xs)
    go xs (LC.Lam x t) =
      Lam $ absFresh x (\y -> go ((x, y) : xs) t)
    go xs (LC.App t s) = App (go xs t) (go xs s)

toLC :: Exp -> LC.LC IdInt
toLC = go []
  where
    go xs (Var a) = LC.Var (getVar a xs)
    go xs (Lam (y :@> t)) =
      let x = nextIdInt xs
       in LC.Lam x (go ((y, x) : xs) t)
    go xs (App t s) = LC.App (go xs t) (go xs s)