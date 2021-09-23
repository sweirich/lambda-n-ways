The DeBruijn module implements the Normal Form function by
using de Bruijn indicies. 

It is originally from Lennart Augustsson's repository
but has been modified to to fit into this setting and 
makes the entire datatype strict.


> module DeBruijn.Lennart(impl, toDB, fromDB, nfd, nfi) where
> import qualified Util.Stats as Stats
> import Util.Syntax.DeBruijn

> import Util.Impl

> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DeBruijn.Lennart"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  


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

> nfi :: Int -> DB -> Stats.M DB
> nfi 0 _e = Stats.done
> nfi _n e@(DVar _) = return e
> nfi n (DLam b) = DLam <$> nfi (n-1) b
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> Stats.count >> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB -> Stats.M DB
> whnfi 0 _e = Stats.done
> whnfi _n e@(DVar _) = return e
> whnfi _n e@(DLam _) = return e
> whnfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case whnf f' of
>         DLam b -> Stats.count >> whnfi (n-1) (instantiate b a)
>         _ -> return $ DApp f' a


----------------------------------------------------------

Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.
This must happen for each occurrence of the substituted term
(as they could be at different binding depths).
(See the 'apply' function.)

> instantiate :: DB -> DB -> DB
> instantiate b a = subst (sub a) b
> {-# INLINE instantiate #-}

> data Sub = Sub {-# UNPACK #-} !Int DB
> sub :: DB -> Sub 
> sub a = Sub 0 a
> {-# INLINE sub #-}

> subst :: Sub -> DB -> DB
> subst s (DVar i) = apply s i
> subst s (DLam e) = DLam (subst (lift s) e)
> subst s (DApp f a) = DApp (subst s f) (subst s a)

> -- | increment all "free" variables by `o`
> -- initially, this operation should be called with n=0
> adjust :: Int -> DB -> Int -> DB
> adjust o e@(DVar j) n | j >= n = DVar (j+o)
>                       | otherwise = e
> adjust o (DLam e) n = DLam (adjust o e (n+1))
> adjust o (DApp f a) n = DApp (adjust o f n) (adjust o a n)

> lift :: Sub -> Sub
> lift (Sub o b) = Sub (o+1) b 
> {-# INLINE lift #-}

> apply :: Sub -> Int -> DB
> apply (Sub o a) i
>  | i == o    = adjust o a 0
>  | i >  o    = DVar (i-1)    -- adjust free variables down (we only call subst through instantiate)
>  | otherwise = DVar i
> {-# INLINE apply #-}
