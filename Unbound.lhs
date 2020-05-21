


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
>         to (L.Var v)   = Var (i2n v)
>         to (L.Lam x b) = Lam (bind (i2n x) (to b))
>         to (L.App f a) = App (to f)(to a)
>


Convert back from deBruijn to the LC type.

> n2i :: Name Exp -> IdInt
> n2i n = (IdInt (fromInteger (name2Integer n)))
>
> i2n :: IdInt -> Name Exp
> i2n (IdInt x) = s2n (show x)

> fromDB :: Exp -> L.LC IdInt
> fromDB = runFreshM . from 
>   where from :: Exp -> FreshM (L.LC IdInt)
>         from (Var n)   = return $ L.Var (n2i n)
>         from (Lam b)   = do
>             (x,a) <- unbind b
>             L.Lam (n2i x) <$> from a
>         from (App f a) = L.App <$> from f <*> from a 

