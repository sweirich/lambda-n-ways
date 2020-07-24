The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> module DeBruijnPar.P(nf,DeBruijnPar.P.aeq,nfd,aeqd,toDB,fromDB,impl) where
> import Data.List(elemIndex)
> import Lambda
> import IdInt
> import Control.DeepSeq

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DB_P"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = error "no nfi"
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

1. smart constructor in lift
2. check for subst (Inc 0)
3. ! in Sub definition
4. ! in DB definition

none: user	0m4.180s
3:    user	0m4.327s
3,4:  user	0m0.846s
2,3,4:

> -- 4 
> data DB = DVar {-# unpack #-} !Int | DLam !DB
>         | DApp !DB  !DB
>   deriving (Eq)
>
> instance NFData DB where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b


> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = aeqd (toDB x) (toDB y)

> aeqd :: DB -> DB -> Bool
> aeqd = (==)


> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam (nfd e)
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (subst (single a) b)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (subst (single a) b)
>         f' -> DApp f' a

Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.

> -- 3 
> data Sub = Inc !Int | Cons !DB !Sub | !Sub :<> !Sub 

> applySub :: Sub -> Int -> DB
> applySub (Inc y) x = DVar (y + x)
> applySub (Cons t ts) x
>    | x < 0     = DVar x
>    | x == 0    = t
>    | otherwise = applySub ts (x - 1)
> applySub (s1 :<> s2) x = subst s2 (applySub s1 x)

> lift :: Sub -> Sub
> lift s   = Cons (DVar 0) (s :<> Inc 1)   -- 1
> single :: DB -> Sub
> single t = Cons t (Inc 0)

> subst :: Sub -> DB -> DB
> subst s (DVar i) = applySub s i
> subst s (DLam e)   = DLam (subst (lift s) e)
> subst s (DApp f a) = DApp (subst s f) (subst s a)


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
>   where from (IdInt n) (DVar i) | i < 0 = Var (IdInt i)
>                                 | i >= n = Var (IdInt i)
>                                 | otherwise = Var (IdInt (n-i-1))
>         from n (DLam b) = Lam n (from (succ n) b)
>         from n (DApp f a) = App (from n f) (from n a)
