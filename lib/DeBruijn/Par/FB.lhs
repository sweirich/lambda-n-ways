The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

This version uses Haskell functions to represent substitutions, but introduces
 a 'Bind' abstract type to delay substitutions at binders.

> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module DeBruijn.Par.FB(nf,DeBruijn.Par.FB.aeq,nfd,toDB,fromDB,nfi, impl) where
> import Data.List(elemIndex)
> import Lambda
> import IdInt
> import Control.DeepSeq
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP

>
> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DeBruijn.Par.FB"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is. 


> data DB = DVar {-# unpack #-} !Int | DLam !(Bind DB)
>         | DApp !DB  !DB
>     deriving (Eq)
>
> instance NFData DB where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b

> instance SubstC DB where
>   var = DVar
>
>   subst s x = go s x where 
>     go _s (DVar i)   = applySub s i
>     go _s (DLam b)   = DLam (substBind s b)
>     go _s (DApp f a) = DApp (go s f) (go s a) 


> {-# SPECIALIZE applySub :: Sub DB -> Int -> DB #-}
> {-# SPECIALIZE nil  :: Sub DB #-}


> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = toDB x == toDB y

> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam (bind (nfd (unbind e)))
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

> nfi :: Int -> DB -> Maybe DB
> nfi 0 e = Nothing
> nfi _n e@(DVar _) = return e
> nfi n (DLam b) = DLam . bind <$> nfi (n-1) (unbind b)
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

-----------------------------------------------------------------

>
> data Bind a = Bind !(Sub a) !a
>
> bind :: SubstC a => a -> Bind a
> bind = Bind nil
> {-# INLINABLE bind #-}

> unbind :: SubstC a => Bind a -> a
> unbind (Bind s a) = subst s a
> {-# INLINABLE unbind #-}

> instantiate :: SubstC a => Bind a -> a -> a
> instantiate (Bind s a) b = subst (s <> single b) a
> {-# INLINABLE instantiate #-}

> substBind :: SubstC a => Sub a -> Bind a -> Bind a
> substBind s2 (Bind s1 e) = Bind (s1 <> lift s2) e
> {-# INLINABLE substBind #-}

> instance (SubstC a, Eq a) => Eq (Bind a) where
>    (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

> instance NFData a => NFData (Bind a) where
>   rnf (Bind s a) = rnf s `seq` rnf a

-----------------------------------------------------------------

> newtype Sub a = Sub (Int -> a) deriving (NFData)

> class SubstC a where
>    var   :: Int -> a
>    subst :: Sub a -> a -> a

> applySub :: SubstC a => Sub a -> Int -> a
> {-# INLINABLE applySub #-}
> applySub (Sub f) = f  

> lift :: SubstC a => Sub a -> Sub a
> {-# INLINABLE lift #-}
> lift s   = consSub (var 0) (s <> incSub 1)
> 
> single :: SubstC a => a -> Sub a
> {-# INLINABLE single #-}
> single t = consSub t nil


> nil :: SubstC a => Sub a 
> {-# INLINABLE nil #-}
> nil = Sub var

> incSub :: SubstC a => Int -> Sub a
> {-# INLINABLE incSub #-}
> incSub y = Sub (\x -> var (y + x))

> consSub :: SubstC a => a -> Sub a -> Sub a
> {-# INLINABLE consSub #-}
> consSub t ts = Sub $ \x -> 
>   if x < 0 then var x
>   else if  x == 0 then t
>   else applySub ts (x - 1)

> instance SubstC a => Semigroup (Sub a) where
>   s1 <> s2  = Sub $ \ x ->  subst s2 (applySub s1 x)
> instance SubstC a => Monoid (Sub a) where
>   mempty  = nil

Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables.  Do not touch
free variables.

> toDB :: LC IdInt -> DB
> toDB = to []
>   where to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
>         to vs (Lam x b) = DLam (bind (to (x:vs) b))
>         to vs (App f a) = DApp (to vs f) (to vs a)

Convert back from deBruijn to the LC type.

> fromDB :: DB -> LC IdInt
> fromDB = from firstBoundId
>   where from (IdInt n) (DVar i) | i < 0     = Var (IdInt i)
>                                 | i >= n    = Var (IdInt i)
>                                 | otherwise = Var (IdInt (n-i-1))
>         from n (DLam b) = Lam n (from (succ n) (unbind b))
>         from n (DApp f a) = App (from n f) (from n a)

---------------------------------------------------------

> instance Show DB where
>     show = renderStyle style . ppLC 0


> ppLC :: Int -> DB -> Doc
> ppLC _ (DVar v)   = text $ "x" ++ show v
> ppLC p (DLam b) = pparens (p>0) $ text "\\." PP.<> ppLC 0 (unbind b)
> ppLC p (DApp f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
