{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

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
import qualified Util.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Nom",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = aeq
    }

-- | Variables are string-labelled names
type Var = Name IdInt

deriving instance (Data IdInt)

deriving newtype instance (Swappable IdInt)

infixl 9 :@

-- | Terms of the untyped lambda-calculus
data Exp
  = -- | Variable
    V Var
  | -- | Application
    Exp :@ Exp
  | -- | Lambda, using abstraction-type
    Lam (KAbs Var Exp)
  deriving (Eq, Generic, Data, Swappable) -- , Show)

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
    V v' | v' == v -> Just t -- If @V v'@, replace with @t@ ...
    _ -> Nothing -- ... otherwise recurse.

-- | weak head normal form of a lambda-term.
whnf :: Exp -> Exp
whnf (f :@ a) =
  case whnf f of
    Lam b' -> whnf $ b' `conc` a
whnf e = e

nf :: Exp -> Exp
nf e@(V _) = e
nf (Lam (x :@> a)) = Lam (x :@> nf a)
nf (f :@ a) =
  case whnf f of
    Lam b -> nf (b `conc` a)
    f' -> nf f' :@ nf a

nfi :: Int -> Exp -> Maybe Exp
nfi 0 _e = Nothing
nfi _n e@(V _) = return e
nfi n (Lam (x :@> e)) = (\t -> (Lam (x :@> t))) <$> nfi (n -1) e
nfi n (f :@ a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam (x :@> b) -> nfi (n -1) (sub x a b)
    _ -> (:@) <$> nfi (n -1) f' <*> nfi (n -1) a

whnfi :: Int -> Exp -> Maybe Exp
whnfi 0 _e = Nothing
whnfi _n e@(V _) = return e
whnfi _n e@(Lam _) = return e
whnfi n (f :@ a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Lam (x :@> b) -> whnfi (n - 1) (sub x a b)
    _ -> return $ f' :@ a

aeq :: Exp -> Exp -> Bool
aeq = aeqd
  where
    aeqd (V v1) (V v2) = v1 == v2
    aeqd (Lam (y :@> b1)) (Lam (z :@> b2)) =
      if y == z
        then aeqd b1 b2
        else aeqd b1 (swpN y z b2)
    aeqd (a1 :@ a2) (b1 :@ b2) =
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
    go xs (LC.Var x) = V (getVar x xs)
    go xs (LC.Lam x t) =
      absFresh
        x
        Lam
        (y :@> go ((x, y) : xs) t)
      where
        y = Name x ()
    go xs (LC.App t s) = go xs t :@ go xs s

toLC :: Exp -> LC.LC IdInt
toLC = go []
  where
    go xs (V a) = LC.Var (getVar a xs)
    go xs (Lam (y :@> t)) =
      let x = nextIdInt xs
       in LC.Lam x (go ((y, x) : xs) t)
    go xs (t :@ s) = LC.App (go xs t) (go xs s)