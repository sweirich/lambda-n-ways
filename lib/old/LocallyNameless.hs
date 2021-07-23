module LocallyNameless where

import Util.IdInt
import Util.IdInt.Set
import Util.Impl

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Locally Nameless",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = error "no nfi",
      impl_aeq = (==)
    }

newtype Bind b = B b deriving (Eq)

data Name = FVar IdInt | BVar Int
  deriving (Eq)

data Exp = Var Name | Lam Name Exp | App Exp Exp
  deriving (Eq)

nfd :: Exp -> Exp
nfd e@(Var _) = e
nfd (Lam x b) = Lam (bind (nfd (unbind b)))
nfd (App f a) =
  case whnf f of
    Lam x b -> nfd (instantiate b a)
    f' -> App (nfd f') (nfd a)

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam x _) = e
whnf (App f a) =
  case whnf f of
    Lam x b -> whnf (instantiate b a)
    f' -> App f' a

---------------------------------

instantiate :: Bind Exp -> Exp -> Exp
instantiate (B a) b = open b a

bind :: Name -> Exp -> Bind Exp
bind n t = B (close n t)

unbind :: Name -> Bind Exp -> Exp
unbind n (B t) = open (Var n) t

open :: Idx a => Exp -> a -> a
open = open' 0

close :: Idx a => Name -> a -> a
close = close' 0

class Idx a where
  open' :: Int -> Exp -> a -> a
  close' :: Int -> Name -> a -> a

class Alpha a where
  aeq :: a -> a -> Bool

class Freevars a where
  fv :: a -> IdIntSet

data IsExp a where
  IsExp :: (a ~ Exp) => IsExp a

class Subst a where
  subst :: Name -> Exp -> a -> a

---------------------------------

instance Idx Name where
  open' x a y = y

  close' c a y@(FVar z) =
    if a == y then BVar c else y
  close' c a y = y

instance Alpha Name where
  aeq = (==)

instance Freevars Name where
  fv (FVar x) = singleton x

instance Subst Name where
  subst _nm _e x = x

--------------------------------

instance Idx b => Idx (Bind b) where
  open' x a (B y) = B (open' (x + 1) a y)
  close' x a (B y) = B (close' (x + 1) a y)

instance (Alpha b) => Alpha (Bind b) where
  (B a) `aeq` (B b) = a `aeq` b

instance Freevars b => Freevars (Bind b) where
  fv (B x) = fv x

instance Subst b => Subst (Bind b) where
  subst x a (B b) = B (subst x a b)

----------------------------------

instance Idx Exp where
  open' x a b@(Var (BVar z)) =
    if x == z then a else b
  open' x a b@(Var (FVar _)) = b
  open' x a (Lam y b) = Lam y (open' x a b)
  open' x a (App b c) = App (open' x a b) (open' x a c)

  close' x a (Var y) = Var (close' x a y)
  close' x a (Lam y b) = Lam y (close' x a b)
  close' x a (App b c) = App (close' x a b) (close' x a c)

instance Alpha Exp where
  aeq (Var x) (Var y) = aeq x y
  aeq (Lam x1 a1) (Lam x2 a2) = aeq a1 a2
  aeq (App a1 b1) (App a2 b2) = aeq a1 a2 && aeq b1 b2
  aeq _ _ = False

instance Subst Exp where
  subst x a b@(Var y)
    | x == y = a
    | otherwise = b
  subst x a (Lam y b) =
    Lam y (subst x a b)
  subst x a (App b1 b2) =
    App (subst x a b1) (subst x a b2)
