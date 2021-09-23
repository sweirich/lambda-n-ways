
Implementation using the Nominal library (available from hackage)

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE DeriveAnyClass #-}
> {-# OPTIONS -fno-warn-orphans #-}

> module Named.Lazy.NominalG(nf,nfi,impl) where
> import Data.List(union, (\\))
> import qualified Util.Syntax.Lambda as LC
> import Util.IdInt ( IdInt )

> import Nominal
> import Prelude hiding ((.))

> import Control.DeepSeq
> import Util.Impl
> import qualified Util.Stats as Stats

>
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Named.Lazy.NominalG"
>           , impl_fromLC = fromLC
>           , impl_toLC   = toLC
>           , impl_nf     = nf
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }

> -- Untyped lambda terms, up to alpha-equivalence.
> data Term = Var Atom | App Term Term | Lam (Bind Atom Term)
>    deriving (Generic, Nominal,Eq)
>
> instance NFData Atom where
>    rnf x = length (show x) == 0 `seq` ()

> instance NFData (Bind Atom Term) where
>    rnf (x :. s) = rnf x `seq` rnf s
> instance NFData Term
>
> getVar :: Eq a => a -> [(a, b)] -> b
> getVar x xs = case lookup x xs of
>                  Just y -> y
>                  Nothing -> error "UNBOUND variable"


> nextIdInt :: [(a,IdInt)] -> IdInt
> nextIdInt []         = toEnum 0
> nextIdInt ((_,y):xs) = max (succ y) (nextIdInt xs)

> fromLC :: LC.LC IdInt -> Term
> fromLC = go [] where
>   go :: [(IdInt,Atom)] -> LC.LC IdInt -> Term
>   go xs (LC.Var x) = Var (getVar x xs)
>   go xs (LC.Lam x t) = with_fresh $ \ y -> Lam (y . go ((x,y):xs) t)
>   go xs (LC.App t s) = App (go xs t) (go xs s)
>
> toLC :: Term -> LC.LC IdInt
> toLC = go [] where
>   go xs (Var a)        = LC.Var (getVar a xs)
>   go xs (Lam (y :. t)) = let x = nextIdInt xs in
>                              LC.Lam x (go ((y,x):xs) t)
>   go xs (App t s)      = LC.App (go xs t) (go xs s)

> -- Capture-avoiding substitution.
> subst ::  Atom -> Term -> Term -> Term
> subst z m (Var x)
>  | x == z    = m
>  | otherwise = Var x
> subst z m (App t s) = App (subst z m t) (subst z m s)
> subst z m (Lam (x :. t)) = Lam (x . subst z m t)


> nf :: Term -> Term
> nf e@(Var _) = e
> nf (Lam (x :. e)) = Lam (x . nf e)
> nf (App f a) =
>     case whnf f of
>         Lam (x :. b) -> nf (subst x a b)
>         f'           -> App (nf f') (nf a)


Compute the weak head normal form.  It is similar to computing the normal form,
but it does not reduce under $\lambda$, nor does it touch an application
that is not a $\beta$-redex.

> whnf :: Term -> Term
> whnf e@(Var _)   = e
> whnf e@(Lam _) = e
> whnf (App f a) =
>     case whnf f of
>         Lam (x :. b) -> whnf (subst x a b)
>         f' -> App f' a


For testing, we can add a "fueled" version

> nfi :: Int -> Term -> Stats.M Term
> nfi 0 _e = Stats.done
> nfi _n e@(Var _) = return  e
> nfi n (Lam (x :. e)) = (\t -> ( Lam (x . t))) <$> nfi (n-1) e
> nfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam (x :. b) -> Stats.count >> nfi (n-1) (subst x a b)
>         _ -> App <$> nfi (n-1) f' <*> nfi (n-1) a


> whnfi :: Int -> Term -> Stats.M Term
> whnfi 0 _e = Stats.done 
> whnfi _n e@(Var _) = return e
> whnfi _n e@(Lam _) = return e
> whnfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam (x :. b) -> Stats.count >> whnfi (n - 1) (subst x a b)
>         _ -> return $ App f' a

