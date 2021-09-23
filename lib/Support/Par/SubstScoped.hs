-- This is a general purpose library for defining substitution for debruijn indices
-- Works will well-scoped representations
{-# LANGUAGE QuantifiedConstraints #-}

module Support.Par.SubstScoped where

import Control.DeepSeq
import Data.Kind (Type)
import Util.Nat

------------------------------------

data Bind a n where
  Bind :: !(Sub a m n) -> !(a ('S m)) -> Bind a n

bind :: a ('S n) -> Bind a n
bind x = Bind (Inc SZ) x
{-# INLINEABLE bind #-}

unbind :: SubstC a => Bind a n -> a ('S n)
unbind (Bind s a) = subst (lift s) a
{-# INLINEABLE unbind #-}

instantiate :: SubstC a => Bind a n -> a n -> a n
instantiate (Bind s a) b = subst (Cons b s) a
{-# INLINEABLE instantiate #-}

substBind :: SubstC a => Sub a n m -> Bind a n -> Bind a m
-- use comp instead of :<>
substBind s2 (Bind s1 e) = Bind (comp s1 s2) e
{-# INLINEABLE substBind #-}

instance (SubstC a, Eq (a ('S n))) => Eq (Bind a n) where
  (Bind s1 x) == (Bind s2 y) = subst (lift s1) x == subst (lift s2) y

------------------------------------

data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Inc :: !(SNat m) -> Sub a n (Plus m n) --  increment by m
  Cons :: (a m) -> !(Sub a n m) -> Sub a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Sub a m n) -> !(Sub a n p) -> Sub a m p --  compose substitutions

infixr 9 :<> -- like usual composition  (.)

class SubstC (a :: Nat -> Type) where
  var :: Idx n -> a n
  subst :: Sub a n m -> a n -> a m

--  Value of the index x in the substitution s
applyS :: SubstC a => Sub a n m -> Idx n -> a m
applyS (Inc m) x = var (shift m x)
applyS (Cons ty _s) FZ = ty
applyS (Cons _ty s) (FS x) = applyS s x
applyS (s1 :<> s2) x = subst s2 (applyS s1 x)
{-# INLINEABLE applyS #-}

nil :: SubstC a => Sub a n n
nil = Inc SZ
{-# INLINEABLE nil #-}

lift :: SubstC a => Sub a n m -> Sub a ('S n) ('S m)
lift s = Cons (var FZ) (s :<> Inc (SS SZ))
{-# INLINEABLE lift #-}

single :: SubstC a => a n -> Sub a ('S n) n
single t = Cons t (Inc SZ)
{-# INLINEABLE single #-}

incSub :: Sub a n ('S n)
incSub = Inc (SS SZ)
{-# INLINEABLE incSub #-}

-- smart constructor for composition
comp :: SubstC a => Sub a m n -> Sub a n p -> Sub a m p
-- this one is difficult to type check
-- comp (Inc k1) (Inc k2)  = Inc (k1 + k2)
comp (Inc SZ) s = s
comp (Inc (SS n)) (Cons _t s) = comp (Inc n) s
comp s (Inc SZ) = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

instance (forall n. NFData (a n)) => NFData (Sub a m1 m2) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

instance (forall n. NFData (a n)) => NFData (Bind a m) where
  rnf (Bind s a) = rnf s `seq` rnf a
