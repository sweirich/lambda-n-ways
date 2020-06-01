The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> module DeBruijnParF(nf,DeBruijnParF.aeq,nfd,aeqd,toDB,fromDB,nfi) where
> import Data.List(elemIndex)
> import Lambda
> import IdInt
> import Control.DeepSeq

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


Bounded versions

> instantiate :: DB -> DB -> DB
> instantiate b a = subst (single a) b

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

> -- 3 
> newtype Sub = Sub (Int -> DB)

> applySub :: Sub -> Int -> DB
> {-# INLINE applySub #-}
> applySub (Sub f) = f  

> lift :: Sub -> Sub
> {-# INLINE lift #-}
> lift s   = consSub (DVar 0) (s <> incSub 1)   -- 1
> single :: DB -> Sub
> {-# INLINE single #-}
> single t = consSub t (incSub 0)

> subst :: Sub -> DB -> DB
> subst s (DVar i)   = applySub s i
> subst s (DLam e)   = DLam (subst (lift s) e)
> subst s (DApp f a) = DApp (subst s f) (subst s a)

> idSub :: Sub 
> {-# INLINE idSub #-}
> idSub = Sub DVar

> incSub :: Int -> Sub 
> {-# INLINE incSub #-}
> incSub y = Sub (\x -> DVar (y + x))

> consSub :: DB -> Sub -> Sub 
> {-# INLINE consSub #-}
> consSub t ts = Sub $ \x -> 
>   if x < 0 then DVar x
>   else if  x == 0 then t
>   else applySub ts (x - 1)

> instance Semigroup Sub where
>   s1 <> s2  = Sub $ \ x ->  subst s2 (applySub s1 x)


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
