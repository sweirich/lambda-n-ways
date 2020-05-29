> module SimpleB(nf,aeq,aeqd,toExp,fromExp,nfd) where
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
> newId vs = case S.lookupMax vs of
>               Just (IdInt x) -> IdInt (x+1)
>               Nothing        -> IdInt 0


Invariants:

1. The variable v will not capture any free variables in the range of the
     stored substitution in the binder. If this could occur, we need to alpha
     vary x to be a fresh variable.
2. The variable v is not a member of the free variables stored in the binding.

> data Bind v e = Bind (Sub v e) (S.Set v) v e

> bind :: IdInt -> Exp -> Bind IdInt Exp
> bind v a = Bind emptySub (S.delete v (freeVars a)) v  a
> {-# INLINABLE bind #-}

> unbind :: Bind IdInt Exp -> (IdInt, Exp)
> unbind (Bind s _fv x a) = (x,subst s a)
> {-# INLINABLE unbind #-}

> instantiate :: Bind IdInt Exp -> Exp -> Exp
> instantiate (Bind s _fv x a) b = subst (comp s (singleSub x b)) a
> {-# INLINABLE instantiate #-}


> freeVarsBind :: Bind IdInt Exp -> S.Set IdInt
> freeVarsBind (Bind s fv _ _) = freeVarsSub s <> fv

> freeVarsSub :: Sub IdInt Exp -> S.Set IdInt
> freeVarsSub = foldMap freeVars


Here we want to push the substitution `s2` through the binder for `x`.
1. what if x is in the dom of s2? then 

> substBind :: Sub IdInt Exp -> Bind IdInt Exp -> Bind IdInt Exp
> substBind s2 b@(Bind s1 fv x e)
>   | M.null s2     = b
>   | M.member x s2 = substBind (M.delete x s2) b
>   | x `elem` freeVarsSub s2  =
>     let fv1 = freeVarsSub s1
>         fv2 = freeVarsSub s2
>         y   = newId (fv `S.union` fv2 `S.union` M.keysSet s2 `S.union` fv1 `S.union` M.keysSet s1)
>         s   = singleSub y (Var x) `comp` s1 `comp` s2
>     in
>         Bind s fv y e
>   | True = Bind (comp s1 s2) fv x e
> {-# INLINABLE substBind #-}


> instance (NFData x, NFData a) => NFData (Bind x a) where
>     rnf (Bind s f x a) = rnf s `seq` rnf f `seq` rnf x `seq` rnf a




-------------------------------------------------------------------

> type Sub = M.Map
 
> emptySub :: Sub x e
> emptySub = M.empty

> singleSub :: x -> e -> Sub x e
> singleSub = M.singleton

> comp :: Sub IdInt Exp -> Sub IdInt Exp -> Sub IdInt Exp
> comp s1 s2 = M.map (subst s1) s2 <> s1


> applySub :: Sub IdInt Exp -> IdInt -> Exp
> applySub s x = M.findWithDefault (Var x) x s



-------------------------------------------------------------------

> data Exp = Var !IdInt | Lam !(Bind IdInt Exp) | App !Exp !Exp
>
> instance NFData Exp where
>    rnf (Var i) = rnf i
>    rnf (Lam d) = rnf d
>    rnf (App a b) = rnf a `seq` rnf b


> freeVars :: Exp -> S.Set IdInt
> freeVars (Var v)   = S.singleton v
> freeVars (Lam b)   = freeVarsBind b
> freeVars (App f a) = freeVars f `S.union` freeVars a

> subst :: Sub IdInt Exp -> Exp -> Exp
> subst s (Var i)   = applySub s i
> subst s (Lam b)   = Lam (substBind s b)
> subst s (App f a) = App (subst s f) (subst s a) 

-------------------------------------------------------------------

> aeq :: LC.LC IdInt -> LC.LC IdInt -> Bool
> aeq x y = aeqd (toExp x) (toExp y)


> nf :: LC.LC IdInt -> LC.LC IdInt
> nf = fromExp . nfd . toExp

Alpha-equivalence

> aeqBind :: Bind IdInt Exp -> Bind IdInt Exp -> Bool
> aeqBind (Bind s1 f1 x1 b1) e2@(Bind s2 f2 x2 b2)
>   | x1 == x2 = aeqd (subst s1 b1) (subst s2 b2)
>   | x1 `elem` freeVarsBind e2 = False
>   | otherwise = aeqd (subst s1 b1) (subst (singleSub x2 (Var x1) `comp` s2) b2)

> aeqd :: Exp -> Exp -> Bool
> aeqd (Var v1)    (Var v2)    = v1 == v2
> aeqd (Lam e1)    (Lam e2)    = aeqBind e1 e2
> aeqd (App a1 a2) (App b1 b2) = aeqd a1 b1 && aeqd a2 b2
> aeqd _ _ = False


Computing the normal form proceeds as usual. 

> nfd :: Exp -> Exp
> nfd e@(Var _) = e
> nfd (Lam b) = Lam (bind x (nfd a)) where (x,a) = unbind b
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

> toExp :: LC.LC IdInt -> Exp
> toExp = to
>   where to (LC.Var v)   = Var v
>         to (LC.Lam x b) = Lam (bind x (to b))
>         to (LC.App f a) = App (to f) (to a)

Convert back from deBruijn to the LC type.

> fromExp :: Exp -> LC.LC IdInt
> fromExp = from 
>   where from (Var i)   = LC.Var i
>         from (Lam b)   = LC.Lam x (from a)
>             where (x,a) = unbind b
>         from (App f a) = LC.App (from f) (from a)

---------------------------------------------------------

> instance Show Exp where
>     show = renderStyle style . ppExp 0


> ppExp :: Int -> Exp -> Doc
> ppExp _ (Var v)   = text $ "x" ++ show v
> ppExp p (Lam b)   = pparens (p>0) $ text ("\\") PP.<> text ("x"++show x) PP.<> text "."
>                                       PP.<> ppExp 0 a where (IdInt x,a) = unbind b
> ppExp p (App f a) = pparens (p>1) $ ppExp 1 f <+> ppExp 2 a


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
