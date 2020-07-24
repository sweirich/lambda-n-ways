> module Impl.NominalB(nf,aeq,aeqd,toDB,fromDB,nfd) where
> import Data.List(elemIndex)
> import qualified Lambda as LC
> import IdInt
> import Control.DeepSeq
> import qualified Data.Map.Strict as M
> import qualified Data.Set as S
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP

Get a variable which is not in the given set.

> newId :: S.Set IdInt -> IdInt
> newId vs = case S.max vs of
>               Just (IdInt x) -> IdInt (x+1)
>               Nothing -> IdInt 0


Invariants:

1. The variable v will not capture any free variables in the range of the
     stored substitution in the binder. If this could occur, we need to alpha
     vary x to be a fresh variable.
2. The variable v is not a member of the free variables stored in the binding.

> data Bind v e = Bind (Subst v e) (Set v) v e

> bind :: v -> a -> Bind v a
> bind v a = Bind emptySub (S.delete v (freeVars a)) a
> {-# INLINABLE bind #-}

> unbind :: Bind v a -> a
> unbind (Bind s _fv _x a) = subst s a
> {-# INLINABLE unbind #-}

> instantiate :: Bind v a -> a -> a
> instantiate (Bind s _fv x a) b = subst (comp s (singleSub x b)) a
> {-# INLINABLE instantiate #-}


> freeVarsBind :: Bind v a -> [v]
> freeVarsBind (Bind s fv _ _) = freeVarsSubst <> fv

> freeVarsSub :: Sub v a -> Set v
> freeVarsSub = M.foldl' (<>) freeVars 


Here we want to push the substitution `s2` through the binder for `x`.
1. what if x is in the dom of s2? then 

> substBind :: Sub v a -> Bind v a -> Bind v a
> substBind s2 b
>   | M.null s2 = b
> substBind s2 b@(Bind s1 fv x e)
>   | M.member x s2             = substBind (M.delete x s2) b
>   | x `elem` fv2 = Bind s fv y e
>       where
>         fv1 = freeVarsSub s1
>         fv2 = freeVarsSub s2
>         y   = newId (fv `union` fv2 `union` keysSet s2 `union` fv1 `union` keysSet s1)
>         s   = singleSub y (Var x) `comp` s1 `comp` s2
>   | otherwise = Bind (comp s1 s2) fv x e
> {-# INLINABLE substBind #-}


> instance (NFData x, NFData a) => NFData Bind x a where
>     rnf (Bind s f x a) = rnf s `seq` rnf f `seq` rnf x `seq` rnf a




-------------------------------------------------------------------

> type Sub = M.Map
 
> emptySub :: Sub x e
> emptySub = M.empty

> singleSub :: Sub x e
> singleSub = M.singleton

> comp :: Sub x v -> Sub x v -> Sub x v
> comp s1 s2 = M.map (subst s1) s2 <> s1


> applySub :: Sub x v -> x -> v
> applySub s x = M.findWithDefault x (Var x) s



-------------------------------------------------------------------

> data Exp = Var !IdInt | Lam !(Bind IdInt Exp) | App !Exp !Exp
>
> instance NFData Exp where
>    rnf (Var i) = rnf i
>    rnf (Lam d) = rnf d
>    rnf (App a b) = rnf a `seq` rnf b


> freeVars :: Exp -> Set IdInt
> freeVars (Var v)   = S.singleton v
> freeVars (Lam b)   = freeVarsBind b
> freeVars (App f a) = freeVars f `union` freeVars a

> subst :: Subst IdInt Exp -> Exp -> Exp
> subst s (Var i)   = applySub s i
> subst s (Lam b)   = Lam (substBind s b)
> subst s (App f a) = App (subst s f) (subst s a) 

-------------------------------------------------------------------

> aeq :: LC.LC IdInt -> LC.LC IdInt -> Bool
> aeq x y = aeqd  M.empty (toExp x) (toExp y)


> nf :: LC IdInt -> LC IdInt
> nf = fromExp . nfd . toExp

Alpha-equivalence

> aeqBind :: Bind v b -> Bind v b -> Bool
> aeqBind (Bind s1 f1 x1 b1) e2@(Bind s2 f2 x2 b2)
>   | x1 == x2 = aeqd (subst s1 b1) (subst s2 b2)
>   | x1 `elem` freeVars e2 = False
>   | otherwise = aeqd (subst s1 b1) (subst (singleSub x2 (Var x1) `comp` s2) b2)

> aeqd :: Exp -> Exp -> Bool
> aeqd m (Var v1) (Var v2) = v1 == v2
> aeqd m (Lam e1) (Lam e2)
>   | v1 == v2  = aeqd m e1 e2
>   | v1 `elem` freeVars e2 = False
>   | otherwise = aeqd (M.insert v2 v1 m) e1 e2
> aeqd m (App a1 a2) (App b1 b2) =
>   aeqd m a1 b1 && aeqd m a2 b2
> aeqd _ _ _ = False


Computing the normal form proceeds as usual. 

> nfd :: Exp -> Exp
> nfd e@(Var _) = e
> nfd (Lam b) = Lam (bind (nfd (unbind b)))
> nfd (App f a) =
>     case whnf f of
>         Lam b -> nfd (instantiate b a)
>         f' -> App (nfd f') (nfd a)

Compute the weak head normal form. 

> whnf :: Exp -> Exp
> whnf e@(Var _) = e
> whnf e@(Lam _) = e
> whnf (App f a) =
>     case whnf f of
>         Lam b -> whnf (instantiate b a)
>         f' -> App f' a

---------------------------------------------------------

> toExp :: LC IdInt -> Exp
> toExp = to []
>   where to vs (LC.Var v@(IdInt i)) = maybe (Var i) Var (elemIndex v vs)
>         to vs (LC.Lam x b) = Lam (bind (to (x:vs) b))
>         to vs (LC.App f a) = App (to vs f) (to vs a)

Convert back from deBruijn to the LC type.

> fromExp :: Exp -> LC IdInt
> fromExp = from firstBoundId
>   where from (IdInt n) (Var i) | i < 0 = Var (IdInt i)
>                                 | otherwise = Var (IdInt (n-i-1))
>         from n (Lam b)   = Lam n (from (succ n) (unbind b))
>         from n (App f a) = App (from n f) (from n a)

---------------------------------------------------------

> instance Show Exp where
>     show = renderStyle style . ppExp 0


> ppExp :: Int -> Exp -> Doc
> ppExp _ (Var v)   = text $ "x" ++ show v
> ppExp p (Lam b)   = pparens (p>0) $ text ("\\.") PP.<> ppExp 0 (unbind b)
> ppExp p (App f a) = pparens (p>1) $ ppExp 1 f <+> ppExp 2 a


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
