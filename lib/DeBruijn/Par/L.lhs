The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

Substitutions are represented as infinite lists

> module DeBruijn.Par.L(nf,DeBruijn.Par.L.aeq,nfd,toDB,fromDB,nfi, impl) where
> import Data.List(elemIndex)
> import Lambda
> import IdInt
> import Control.DeepSeq
>
> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DeBruijn.Par.L"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.


> data DB = DVar {-# unpack #-} !Int | DLam !DB
>         | DApp !DB  !DB
>   deriving (Eq)
>
> instance NFData DB where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b

> subst :: Sub -> DB -> DB
> subst s (DVar i)   = applySub s i
> subst s (DLam e)   = DLam (subst (lift s) e)
> subst s (DApp f a) = DApp (subst s f) (subst s a)

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
>         DLam b -> nfd (instantiate b a)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate b a)
>         f' -> DApp f' a


Bounded versions

> instantiate :: DB -> DB -> DB
> instantiate b a = subst (single a) b
> {-# INLINABLE instantiate #-}

> nfi :: Int -> DB -> Maybe DB
> nfi 0 _e = Nothing
> nfi _n e@(DVar _) = return e
> nfi n (DLam b) = DLam <$> nfi (n-1) b
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB -> Maybe DB
> whnfi 0 _e = Nothing
> whnfi _n e@(DVar _) = return e
> whnfi _n e@(DLam _) = return e
> whnfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case whnf f' of
>         DLam b -> whnfi (n-1) (instantiate b a)
>         _ -> return $ DApp f' a




> -- 3 
> type Sub = [DB]

> applySub :: Sub -> Int -> DB
> applySub s i = s !! i
> {-# INLINE applySub #-}

> -- identity substitution, leaves all variables alone
> nilSub :: Sub 
> nilSub =  go 0 where
>    go i = DVar i : go (i+1)
> {-# INLINE nilSub #-}

> -- increment everything by 1
> weakSub :: Sub
> {-# INLINE weakSub #-}
> weakSub = tail nilSub

> -- singleton, replace 0 with t, leave everything
> -- else alone
> single :: DB -> Sub
> {-# INLINE single #-}
> single t = t `consSub` nilSub


> consSub :: DB -> Sub -> Sub
> {-# INLINE consSub #-}
> consSub x s = x : s



> -- Used in substitution when going under a binder
> lift :: Sub -> Sub
> lift s = DVar 0 : (s `composeSub` weakSub)
> {-# INLINE lift #-}

> composeSub :: Sub -> Sub -> Sub
> composeSub s1 s2 = map (subst s2) s1
> {-# INLINE composeSub #-}

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
