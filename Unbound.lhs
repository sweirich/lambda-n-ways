


> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE TemplateHaskell #-}
> module Unbound(nf) where
> import qualified Lambda as L
> import IdInt
>
> import Control.Monad

> import Unbound.LocallyNameless


> data Exp = Var (Name Exp)
>          | Lam (Bind (Name Exp) Exp)
>         | App Exp Exp
>  deriving Show

-- Use RepLib to derive representation types

> $(derive [''Exp])

-- | With representation types, tbe default implementation of Alpha
-- provides alpha-equivalence and free variable calculation.

> instance Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.

> instance Subst Exp Exp where
>   isvar (Var x) = Just (SubstName x)
>   isvar _       = Nothing


> nf :: L.LC IdInt -> L.LC IdInt
> nf = fromDB . runFreshM .  nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: Exp -> FreshM Exp
> nfd e@(Var _) = return e
> nfd (Lam e)   =
>   do (x, e') <- unbind e
>      e1 <- nfd e'
>      return $ Lam (bind x e1)
> nfd (App f a) =
>     case whnf f of
>         Lam b -> nfd (substBind b a)
>         f' -> App <$> nfd f' <*> nfd a

Compute the weak head normal form.

> whnf :: Exp -> Exp
> whnf e@(Var _) = e
> whnf e@(Lam _) = e
> whnf (App f a) = 
>     case whnf f of
>         Lam b -> whnf (substBind b a)
>         f' -> App f' a


Convert from LC type to DB type (try to do this in linear time??)

> toDB :: L.LC IdInt -> Exp
> toDB = to
>   where to :: L.LC IdInt -> Exp
>         to (L.Var (IdInt v))   = Var (s2n (show v))
>         to (L.Lam (IdInt x) b) = Lam (bind (s2n (show x)) (to b))
>         to (L.App f a)         = App (to f)(to a)
>


Convert back from deBruijn to the LC type.

> n2i :: Name Exp -> IdInt
> n2i n = (IdInt (fromInteger (name2Integer n)))
>
> i2n :: IdInt -> Name Exp
> i2n (IdInt x) = s2n (show x)

> fromDB :: Exp -> L.LC IdInt
> fromDB = from firstBoundId
>   where from :: IdInt -> Exp -> L.LC IdInt
>         from _ (Var n)   = L.Var (n2i n)
>         from n (Lam b)   = L.Lam n (from (succ n) (substBind b (Var (i2n n))))
>         from n (App f a) = L.App (from n f) (from n a) 

