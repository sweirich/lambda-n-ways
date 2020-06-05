The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

It uses parallel substitutions and explcit substitutions stored in the term.

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> module DeBruijnScoped(nf,DeBruijnScoped.aeq, toDB, fromDB, nfd, nfi, impl) where
> import Lambda
> import IdInt
> import SubstScoped
> import Control.DeepSeq

> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Data.Maybe(fromJust)

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Scoped"
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
> data DB n where
>   DVar :: Idx n -> DB n
>   DLam :: !(Bind DB n) -> DB n
>   DApp :: !(DB n) -> !(DB n) -> DB n

> instance NFData (DB a) where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b


Alpha equivalence requires pushing delayed substitutions into the terms

> instance Eq (DB n) where
>    DVar x == DVar y = x == y
>    DLam x == DLam y = x == y
>    DApp x1 x2 == DApp y1 y2 = x1 == y1 && x2 == y2
>    _ == _           = False

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = aeqd (toDB x) (toDB y)

> aeqd :: DB n -> DB n -> Bool
> aeqd = (==)

> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual. Should never return a delayed substitution anywhere in the term.

> nfd :: DB n -> DB n
> nfd e@(DVar _) = e
> nfd (DLam b) = DLam (bind (nfd (unbind b)))
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (instantiate b a)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form. Should never return a delayed substitution at the top level.

> whnf :: DB n -> DB n
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate b a)
>         f' -> DApp f' a


> nfi :: Int -> DB n -> Maybe (DB n)
> nfi 0 e = Nothing
> nfi n e@(DVar _) = return e
> nfi n (DLam b) = DLam . bind <$> nfi (n-1) (unbind b)
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB n -> Maybe (DB n)
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

> -- push the substitution in one level
> instance SubstC DB where
>   var = DVar
>
>   -- 3 -- subst (Inc 0) e    = e   -- can discard an identity substitution
>   subst s (DVar i)   = applyS s i
>   subst s (DLam b)   = DLam (substBind s b)
>   subst s (DApp f a) = DApp (subst s f) (subst s a) 



Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. 

> toDB :: LC IdInt -> DB Z
> toDB = to [] 
>   where to :: [(IdInt, Idx n)] -> LC IdInt ->  DB n
>         to vs (Var v)   = DVar (fromJust (lookup v vs))
>         to vs (Lam v b) = DLam (bind b') where
>              b' = to ((v,FZ):mapSnd FS vs) b
>         to vs (App f a) = DApp (to vs f) (to vs a)

Convert back from deBruijn to the LC type. Note, all variables must be in scope.

> fromDB :: DB n -> LC IdInt
> fromDB = from []
>   where from :: [(Idx n, IdInt)] -> DB n -> LC IdInt
>         from vs (DVar v)   = Var  (fromJust (lookup v vs))
>         from vs (DLam b)   = Lam n (from vs' (unbind b)) where
>                (n,vs') = next vs
>         from vs (DApp f a) = App (from vs f) (from vs a) 

> next :: [(Idx n, IdInt)] -> (IdInt, [(Idx (S n), IdInt)])
> next [] = (firstBoundId, [(FZ, firstBoundId)])
> next ((_n, i):rest) = (succ i, (FZ, succ i): mapFst FS rest)

> mapFst :: (a -> b) -> [(a,c)] -> [(b,c)]
> mapFst f = map (\ (v,i) -> (f v, i))
>
> mapSnd :: (a -> b) -> [(c,a)] -> [(c,b)]
> mapSnd f = map (\ (v,i) -> (v, f i))

---------------------------------------------------------

> instance Show (DB n) where
>     show = renderStyle style . ppLC 0


> ppLC :: Int -> DB n -> Doc
> ppLC _ (DVar v)   = text $ "x" ++ show v
> ppLC p (DLam b) = pparens (p>0) $ text ("\\.") PP.<> ppLC 0 (unbind b)
> ppLC p (DApp f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a


> ppS :: Sub DB n m -> Doc
> ppS (Inc k)     = text ("+" ++ show k)
> ppS (Cons t s)  = ppLC 0 t <+> text "<|" <+> ppS s
> ppS (s1 :<> s2) = ppS s1 <+> text "<>" <+> ppS s2


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
