The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> module DeBruijn(nf,DeBruijn.aeq, toDB, fromDB, nfd, nfi, impl) where
> import Data.List(elemIndex)
> import Lambda
> import IdInt
> import Control.DeepSeq

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DB"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

> data DB = DVar !Int | DLam DB | DApp DB DB
>   deriving (Eq)

> instance NFData DB where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = toDB x == toDB y

> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam (nfd e)
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (subst 0 a b)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (subst 0 a b)
>         f' -> DApp f' a


Bounded versions

> instantiate :: DB -> DB -> DB
> instantiate b a = subst 0 a b

> nfi :: Int -> DB -> Maybe DB
> nfi 0 e = Nothing
> nfi n e@(DVar _) = return e
> nfi n (DLam b) = DLam <$> nfi (n-1) b
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB -> Maybe DB
> whnfi 0 e = Nothing
> whnfi n e@(DVar _) = return e
> whnfi n e@(DLam _) = return e
> whnfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case whnf f' of
>         DLam b -> whnfi (n-1) (instantiate b a)
>         _ -> return $ DApp f' a



Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.

> subst :: Int -> DB -> DB -> DB
> subst o s v@(DVar i) | i == o = adjust 0 s
>                      | i >  o = DVar (i-1)
>                      | otherwise = v
>   where adjust n e@(DVar j) | j >= n = DVar (j+o)
>                             | otherwise = e
>         adjust n (DLam e) = DLam (adjust (n+1) e)
>         adjust n (DApp f a) = DApp (adjust n f) (adjust n a)
> subst o s (DLam e) = DLam (subst (o+1) s e)
> subst o s (DApp f a) = DApp (subst o s f) (subst o s a)

Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables.  Do not touch
free variables.

> toDB :: LC IdInt -> DB
> toDB = to []
>   where to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
>         to vs (Lam x b) = DLam (to (x:vs) b)
>         to vs (App f a) = DApp (to vs f) (to vs a)

Convert back from deBruijn to the LC type.

> fromDB :: DB -> LC IdInt
> fromDB = from firstBoundId
>   where from (IdInt n) (DVar i) | i < 0     = Var (IdInt i)
>                                 | i >= n    = Var (IdInt i)
>                                 | otherwise = Var (IdInt (n-i-1))
>         from n (DLam b) = Lam n (from (succ n) b)
>         from n (DApp f a) = App (from n f) (from n a)
