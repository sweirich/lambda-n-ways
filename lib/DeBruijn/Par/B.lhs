The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

It uses parallel substitutions and explicit substitutions stored in the term.

potential optimizations

1. smart constructor in subst s2 (Bind s1 a)
2. smart constructor in lift
3. check for subst (Inc 0)
4. ! in Sub definition
5. ! in DB definition


NONE:   user	0m6.655s
1:      user	0m0.038s   (almost as fast at H, at user	0m0.030s)
1,2:    user	0m0.565s
2:      user    0m6.262s
1,3:    user	0m0.040s
1,4:    user	0m0.036s
1,4,5:  user	0m0.026s   (faster than H!)
1,2,4,5: (took too long!)
1,3,4,5: user	0m0.027s
1,3,4,5,6: user	0m0.010s
user	0m0.009s

> module DeBruijn.Par.B(nf,DeBruijn.Par.B.aeq,toDB,fromDB,nfd,nfi, impl) where
> import Data.List(elemIndex)
> import Util.Lambda
> import Util.IdInt
> import Control.DeepSeq
>
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP

> import Util.Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "DeBruijn.Par.B"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

This version adds an explicit substitution to the data type that allows
the sub to be suspended (and perhaps optimized).

> -- 5 -- make fields strict
> data DB = DVar {-# unpack #-} !Int | DLam !(Bind DB)
>         | DApp !DB !DB
>    deriving (Eq)
> 
> instance NFData DB where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b


Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.

> -- push the substitution in one level
> instance SubstC DB where
>   var = DVar
>   {-# INLINABLE var #-}
>
>   -- 3 -- subst (Inc 0) e    = e   -- can discard an identity substitution
>   subst s x = go s x where 
>     go _s (DVar i)   = applySub s i
>     go _s (DLam b)   = DLam (substBind s b)
>     go _s (DApp f a) = DApp (go s f) (go s a) 
>   {-# INLINABLE subst #-}

> {-# SPECIALIZE applySub :: Sub DB -> Int -> DB #-}
> {-# SPECIALIZE nil :: Sub DB #-}
> {-# SPECIALIZE comp :: Sub DB -> Sub DB -> Sub DB #-}
> 
> {-# SPECIALIZE lift :: Sub DB -> Sub DB #-}
> {-# SPECIALIZE single :: DB -> Sub DB #-}
> {-# SPECIALIZE unbind :: Bind DB -> DB #-}
> {-# SPECIALIZE instantiate :: Bind DB -> DB -> DB #-}
> {-# SPECIALIZE substBind :: Sub DB -> Bind DB -> Bind DB #-}



> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = toDB x == toDB y


> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual. Should never return a delayed
 substitution anywhere in the term.

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam b) = DLam (bind (nfd (unbind b)))
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> 
>            nfd (instantiate b a)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form. Should never return a delayed substitution at the top level.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate b a)
>         f' -> DApp f' a


Bounded versions

> nfi :: Int -> DB -> Maybe DB
> nfi 0 _e = Nothing
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
>         from n (DLam b)   = Lam n (from (succ n) (unbind b))
>         from n (DApp f a) = App (from n f) (from n a)

---------------------------------------------------------

> instance Show DB where
>     show = renderStyle style . ppLC 0


> ppLC :: Int -> DB -> Doc
> ppLC _ (DVar v)   = text $ "x" ++ show v
> ppLC p (DLam b) = pparens (p>0) $ text "\\." PP.<> ppLC 0 (unbind b)
> ppLC p (DApp f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a


> ppS :: Sub DB -> Doc
> ppS (Inc k)     = text ("+" ++ show k)
> ppS (Cons t s)  = ppLC 0 t <+> text "<|" <+> ppS s
> ppS (s1 :<> s2) = ppS s1 <+> text "<>" <+> ppS s2


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d

-------------------------------------------------------------
-------------------------------------------------------------

> data Bind a = Bind !(Sub a) !a deriving (Show)

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
>   -- NOTE: use comp instead of :<>
> substBind s2 (Bind s1 e) = Bind (s1 <> lift s2) e
> {-# INLINABLE substBind #-}

> instance (SubstC a, Eq a) => Eq (Bind a) where
>    (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

> instance NFData a => NFData (Bind a) where
>   rnf (Bind s a) = rnf s `seq` rnf a


> -- 4 -- make all fields strict
> -- NOTE: do *not* make first argument of Cons strict. See lams/regression1.lam
> data Sub a = Inc {-# UNPACK #-} !Int
>       | Cons a !(Sub a)
>       | !(Sub a) :<> !(Sub a)
>    deriving Show
> 
>
> class SubstC a where
>    var   :: Int -> a
>    subst :: Sub a -> a -> a

> applySub :: SubstC a => Sub a -> Int -> a
> applySub (Inc y)     x = var (y + x)
> applySub (Cons t ts) x
>            | x > 0     = applySub ts (x - 1) 
>            | x == 0    = t
>            | otherwise = var x 
> applySub (s1 :<> s2) x = subst s2 (applySub s1 x)
> {-# INLINABLE applySub #-}


> nil :: SubstC a => Sub a
> nil = Inc 0
> {-# INLINABLE nil #-}

NOTE: adding a smart constructor in lift really slows things down!

> lift :: SubstC a => Sub a -> Sub a
> lift s   = Cons (var 0) (s :<> Inc 1)
> {-# INLINABLE lift #-}


> single :: SubstC a => a -> Sub a
> single t = Cons t nil
> {-# INLINABLE single #-}


> -- smart constructor for composition
> comp :: SubstC a => Sub a -> Sub a -> Sub a
> comp (Inc k1) (Inc k2)  = Inc (k1 + k2)
> comp (Inc 0) s       = s
> comp (Inc n) (Cons _t s)
>           | n > 0 = comp (Inc (n - 1)) s
> comp s (Inc 0)   = s
> comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
> comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
> comp s1 s2 = s1 :<> s2
> {-# INLINABLE comp #-}


> instance SubstC a => Semigroup (Sub a) where
>   (<>) = comp
> instance SubstC a => Monoid (Sub a) where
>   mempty  = nil
>   mappend = (<>)

> instance NFData a => NFData (Sub a) where
>   rnf (Inc i) = rnf i
>   rnf (Cons t ts) = rnf t `seq` rnf ts
>   rnf (s1 :<> s2) = rnf s1 `seq` rnf s2


