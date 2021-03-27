The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

It uses parallel substitutions and explicit substitutions stored in the term.

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> module DeBruijnPar.ScopedImpl(nf,DeBruijnPar.Scoped.aeq, toDB, fromDB, nfd, nfi, impl) where
> import LambdaImpl
> import IdInt
> import DeBruijnPar.SubstScoped (Idx, Nat(..), Sub(..))
> import qualified DeBruijnPar.SubstScoped as SS
> import Control.DeepSeq

> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Data.Maybe(fromJust)

> {-
> import Control.Monad.State.Strict (MonadState)
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Scoped"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = (==)
>        }
> -}

> newtype DB n = DB (LC (Idx n)) deriving (NFData, Eq) 

> instance Impl (Idx n) where
>   type Bind (Idx n) (LC (Idx n)) = SS.Bind DB n
>   type Subst (Idx n) (LC (Idx m)) = SS.Sub DB n m
>   aeq = undefined
>   bind = undefined
>   unbind = undefined
>   instantiate = undefined


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

This version adds an explicit substitution to the data type that allows
the sub to be suspended (and perhaps optimized).

> -- 5 -- make fields strict
> {-
> data DB n where
>   DVar :: Idx n -> DB n
>   DLam :: !(Bind DB n) -> DB n
>   DApp :: !(DB n) -> !(DB n) -> DB n
> -}

> {-
> instance NFData (DB a) where
>    rnf (DVar i) = rnf i
>    rnf (DLam d) = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b
> -}

Alpha equivalence requires pushing delayed substitutions into the terms

> {-
> instance Eq (DB n) where
>    DVar x == DVar y = x == y
>    DLam x == DLam y = x == y
>    DApp x1 x2 == DApp y1 y2 = x1 == y1 && x2 == y2
>    _ == _           = False
> -}

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = aeqd (toDB x) (toDB y)

> aeqd :: DB n -> DB n -> Bool
> aeqd = (==)

> {-}
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



 > data St = St { numSubsts :: Int, tmsIn :: [LC IdInt] }
 
> iSubst :: MonadState St m => IdInt -> DB n -> DB n -> m (DB n)
> iSubst x a b = do
>   s <- get
>   put (s { numSubsts = numSubsts s + 1 } { tmsIn = a : tmsIn s })
>   return (subst x a b)

> type M a = StateT St (Either String) a

> iNf :: Int -> DB n -> Maybe (DB n, St)
> iNf i z = hush $ runStateT (nfm i z) (St 0 [])

> hush :: Either a b -> Maybe b
> hush = either (const Nothing) Just


> nfm :: (MonadState St m, MonadError String m) => Int -> DB n -> m (DB n)
> nfm 0 _e         = throwError "timeout"
> nfm _n e@(DVar _) = return  e
> nfm n (DLam b) = DLam . bind <$> nfm (n-1) (unbind b)
> nfm n (DApp f a) = do
>     f' <- whnfm (n - 1) f 
>     case f' of
>         DLam x b -> do b' <- iSubst x a b
>                        nfm (n-1) b'
>         _ -> DApp <$> nfm (n-1) f' <*> DLam . bind <$> nfm (n-1) a


> whnfm :: (MonadState St m, MonadError String m) => Int -> DB n -> m (DB n)
> whnfm 0 _e = throwError "timeout"
> whnfm _n e@(Var _) = return e
> whnfm _n e@(Lam _ _) = return e
> whnfm n (App f a) = do
>     f' <- whnfm (n - 1) f 
>     case f' of
>         Lam x b -> do b' <- iSubst x a b
>                       whnfm (n - 1) b'
>         _ -> return $ App f' a
> -}


Substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.

> -- push the substitution in one level
> instance SS.SubstC DB where
>   var = DVar
>
>   subst s (DB a) = DB (subst' s a) where
>     subst' s (Var i)   = applyS s i
>     subst' s (Lam b)   = Lam (substBind s b)
>     subst' s (App f a) = App (subst' s f) (subst' s a) 



Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. 

> toDB :: LC IdInt -> LC (Idx Z)
> toDB = to [] 
>   where to :: [(IdInt, Idx n)] -> LC IdInt ->  DB n
>         to vs (Var v)   = DVar (fromJust (lookup v vs))
>         to vs (Lam v b) = DLam (bind b') where
>              b' = to ((v,FZ):mapSnd FS vs) b
>         to vs (App f a) = DApp (to vs f) (to vs a)

Convert back from deBruijn to the LC type. 


> fromDB :: LC (Idx n) -> LC IdInt
> fromDB (DB x)= from firstBoundId x
>   where from :: IdInt -> DB n -> LC IdInt
>         from (IdInt n) (Var i) | toInt i < 0     = Var (IdInt $ toInt i)
>                                 | toInt i >= n    = Var (IdInt $ toInt i)
>                                 | otherwise = Var (IdInt (n-(toInt i)-1))
>         from n (Lam b)   = Lam n (from (succ n) (unbind b))
>         from n (App f a) = App (from n f) (from n a)



> next :: [(Idx n, IdInt)] -> (IdInt, [(Idx (S n), IdInt)])
> next []             = (firstBoundId, [(FZ, firstBoundId)])
> next ((_n, i):rest) = (succ i,        (FZ, succ i): mapFst FS rest)

> mapFst :: (a -> b) -> [(a,c)] -> [(b,c)]
> mapFst f = map (\ (v,i) -> (f v, i))
>
> mapSnd :: (a -> b) -> [(c,a)] -> [(c,b)]
> mapSnd f = map (\ (v,i) -> (v, f i))

---------------------------------------------------------

> instance Show (DB n) where
>     show = renderStyle style . ppLC 0


> ppLC :: Int -> DB n -> Doc
> ppLC _ (Var v)   = text $ "x" ++ show v
> ppLC p (Lam b) = pparens (p>0) $ text ("\\.") PP.<> ppLC 0 (unbind b)
> ppLC p (App f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a


> ppS :: SS.Sub DB n m -> Doc
> ppS (Inc k)     = text ("+" ++ show k)
> ppS (Cons t s)  = ppLC 0 t <+> text "<|" <+> ppS s
> ppS (s1 :<> s2) = ppS s1 <+> text "<>" <+> ppS s2


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
