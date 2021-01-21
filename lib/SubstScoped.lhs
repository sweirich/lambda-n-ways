
This is a general purpose library for defining substitution for debruijn indices

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE QuantifiedConstraints #-}
> 
> module SubstScoped where
>
> import Data.Kind (Type)
> import Control.DeepSeq

> ------------------------------------

> data Nat = Z | S Nat
>   deriving (Eq,Show)
>
> data SNat n where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)
>
> type family Plus n m where
>    Plus Z n     = n
>    Plus (S m) n = S (Plus m n)

> instance Show (SNat m) where
>    show SZ     = "SZ"
>    show (SS n) = "(SS " ++ show n ++ ")"

> ------------------------------------

> data Idx :: Nat -> Type where
>    FZ :: Idx (S n)
>    FS :: Idx n -> Idx (S n)

> instance Eq (Idx n) where
>    FZ == FZ = True
>    (FS n) == (FS m) = n == m
>    _ == _ = False

> instance Show (Idx n) where
>    show FZ = "FZ"
>    show (FS n) = "(FS " ++ show n ++ ")"

> toInt :: Idx n -> Int
> toInt FZ     = 0
> toInt (FS n) = 1 + toInt n


> shift :: SNat m -> Idx n -> Idx (Plus m n)
> shift SZ x = x
> shift (SS m) x = FS (shift m x)


> ------------------------------------

> data Bind a n where
>    Bind :: !(Sub a m n) -> !(a (S m)) -> Bind a n

> bind :: a (S n) -> Bind a n
> bind x = Bind (Inc SZ) x
> {-# INLINABLE bind #-}

> unbind :: SubstC a => Bind a n -> a (S n)
> unbind (Bind s a) = subst (lift s) a
> {-# INLINABLE unbind #-}

> instantiate :: SubstC a => Bind a n -> a n -> a n
> instantiate (Bind s a) b = subst (Cons b s) a
> {-# INLINABLE instantiate #-}

> substBind :: SubstC a => Sub a n m -> Bind a n -> Bind a m
>   -- use comp instead of :<>
> substBind s2 (Bind s1 e) = Bind (comp s1 s2) e
> {-# INLINABLE substBind #-}

> instance (SubstC a, Eq (a (S n))) => Eq (Bind a n) where
>    (Bind s1 x) == (Bind s2 y) = subst (lift s1) x == subst (lift s2) y

> ------------------------------------

> data Sub (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
>    Inc   :: !(SNat m) -> Sub a n (Plus m n)              --  increment by m
>    Cons  :: (a m) -> !(Sub a n m) -> Sub a (S n) m        --  extend a substitution (like cons)
>    (:<>) :: !(Sub a m n) -> !(Sub a n p) -> Sub a m p     --  compose substitutions

> infixr :<>    -- like usual composition  (.)

> class SubstC (a :: Nat -> Type) where
>   var   :: Idx n -> a n
>   subst :: Sub a n m -> a n -> a m


> --  Value of the index x in the substitution s
> applyS :: SubstC a => Sub a n m -> Idx n -> a m
> applyS (Inc m)          x  = var (shift m x)
> applyS (Cons ty _s)    FZ  = ty
> applyS (Cons _ty s) (FS x) = applyS s x
> applyS (s1 :<> s2)      x  = subst s2 (applyS s1 x)
> {-# INLINABLE applyS #-}


> nil :: SubstC a => Sub a n n
> nil = Inc SZ
> {-# INLINABLE nil #-}

> lift :: SubstC a => Sub a n m -> Sub a (S n) (S m)
> lift s   = Cons (var FZ) (s :<> Inc (SS SZ))
> {-# INLINABLE lift #-}

> single :: SubstC a => a n -> Sub a (S n) n
> single t = Cons t (Inc SZ)
> {-# INLINABLE single #-}

> incSub :: Sub a n (S n)
> incSub = Inc (SS SZ)
> {-# INLINABLE incSub #-}

> -- smart constructor for composition
> comp :: SubstC a => Sub a m n -> Sub a n p  -> Sub a m p
> -- this one is difficult to type check
> -- comp (Inc k1) (Inc k2)  = Inc (k1 + k2)
> comp (Inc SZ) s       = s
> comp (Inc (SS n)) (Cons t s) = comp (Inc n) s
> comp s (Inc SZ)   = s
> comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
> comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
> comp s1 s2 = s1 :<> s2
> {-# INLINABLE comp #-}


> instance (forall n. NFData (a n)) => NFData (Sub a m1 m2) where
>   rnf (Inc i) = rnf i
>   rnf (Cons t ts) = rnf t `seq` rnf ts
>   rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

> instance (forall n. NFData (a n)) => NFData (Bind a m) where
>   rnf (Bind s a) = rnf s `seq` rnf a

> instance NFData (Idx a) where
>   rnf FZ = ()
>   rnf (FS s) = rnf s

> instance NFData (SNat a) where
>   rnf SZ = ()
>   rnf (SS s) = rnf s
