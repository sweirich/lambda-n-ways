This module is trying to make a "delayed" substitution version of the "Simple" implementation. 

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module SimpleB(nf,aeq,aeqd,toExp,fromExp,nfd,nfi) where
> import qualified Lambda as LC
> import IdInt
> import Control.DeepSeq
> import qualified Data.Map.Strict as M
> import qualified Data.Set as S
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Debug.Trace

Get a variable which is not in the given set.

> newId :: (Atom v) => S.Set v -> v
> newId vs = case S.lookupMax vs of
>               Just v   -> succ v
>               Nothing  -> toEnum 0


> class (Enum v, Ord v, Show v) => Atom v 
> instance Atom IdInt


A class of types that can calculate free variables and
substitute. 


> class Atom v => FreeVars v e where
>   freeVars :: e -> S.Set v
>   boundVars :: e -> S.Set v

> class (Atom v, Show a) => Subst v a e where
>   subst    :: Sub v a -> e -> e
>
> class Atom v => Var v e where
>   var      :: v -> e

-------------------------------------------------------------------

In this implementation we cache substitutions and fv sets at binders. That
means that we don't need to recalculate them and that we can combine
substitutions together.


> data Bind v e = Bind { bind_subst :: Sub v e,
>                        bind_fvs   :: S.Set v,
>                        bind_bvs   :: S.Set v,
>                        bind_var   :: v,
>                        bind_body  :: e }

Invariants:

1. bind_fvs is cached freeVars of e, minus v

2. bind_bvs is cached boundVars of e

3. The domain of the bind_subst is a subset of bind_fvs

3. The freeVars of the bind_subst do not include v (i.e. no capture).
   (If this would happen when constructing a bind, we will freshen v to v'
   and extend the substitution with v -> v', in the case that v is free in e.)

> validBind :: (Ord v, FreeVars v e) => Bind v e -> Bool
> validBind b@Bind{} =
>    bind_fvs b == S.delete (bind_var b) (freeVars  (bind_body b)) &&
>    -- bind_bvs b == boundVars (bind_body b) &&
>    M.keysSet (bind_subst b) `S.isSubsetOf` bind_fvs b &&
>    bind_var b `notElem` freeVars (bind_subst b)
> 

> bind :: FreeVars v e => v -> e -> Bind v e
> bind v a = Bind emptySub (S.delete v (freeVars a)) (boundVars a) v a
> {-# INLINABLE bind #-}

> unbind :: Subst v e e => Bind v e -> (v, e)
> unbind (Bind s _fv _bv x a) = (x,subst s a)
> {-# INLINABLE unbind #-}

> instantiate :: (Show v, Show e, Subst v e e) => Bind v e -> e -> e
> instantiate (Bind s _fv _bv x a) b =
>      subst (comp s (singleSub x b)) a
> {-# INLINABLE instantiate #-}


> instance (FreeVars v e) => FreeVars v (Bind v e) where
>   freeVars (Bind s fv _ _ _) = freeVars s <> (fv S.\\ M.keysSet s)
>   boundVars (Bind s _ bv x _) = boundVars s <> bv <> S.singleton x
>
> instance (Var v e, FreeVars v e, Subst v e e, Show v, Show e) => Subst v e (Bind v e) where 
>   subst s2 b@(Bind s1 fv bv x e)
>        | M.null s2     = b
>        | M.member x s2 = {- trace ("Removing " ++ show x ++ " from " ++ show s2
>                          ++ "\n when substituting into \\" ++ show x ++ "." ++ show (subst s1 e)) $ -}
>                          subst (M.delete x s2) b
>        | x `elem` fv2 =  {- trace ("alpha-varying " ++ "\\" ++ show x ++ "." ++ show (subst s1 e)
>                                ++ "\n with freeVars " ++ show (freeVars b :: S.Set v)
>                                ++ "\n when substituting with s2' " ++ show s2'
>                                ++ "\n result is " ++ "\\ " ++ show y ++ "." ++ show (subst s' e)
>                                ++ "\n s1  was " ++ show s1
>                                ++ "\n fv  was " ++ show fv
>                                ++ "\n e   was " ++ show e
>                                ++ "\n fv2 was " ++ show fv2
>                                ++ "\n s   is  " ++ show s
>                                ++ "\n s'  is  " ++ show s'
>                                ++ "\n vs  is  " ++ show vs
>                                ++ "\n valid is " ++ show (validBind (Bind s' fv bv y e))) $  -}
>                          Bind s' fv bv y e
>        | otherwise     = {- trace ("NO alpha-vary for " ++ "\\" ++ show x ++ "." ++ show (subst s1 e)
>                                ++ "\n with freeVars " ++ show (freeVars b :: S.Set v)
>                                ++ "\n when substituting with s2 " ++ show s2
>                                ++ "\n result is " ++ "\\" ++ show x ++ "." ++ show (subst s1s2' e)
>                                ++ "\n fv  was " ++ show fv
>                                ++ "\n e   was " ++ show e
>                                ++ "\n s1  was " ++ show s1
>                                ++ "\n s1s2' is " ++ show s1s2'
>                                ++ "\n fv2 was " ++ show fv2
>                                ++ "\n valid is " ++ show (validBind (Bind s1s2' fv bv x e))) $  -}
>                          Bind s1s2' fv bv x e
>     where fv1 = freeVars s1
>           fv2 = freeVars s2'
>           vs  = fv `S.union` fv2 `S.union`
>                 M.keysSet s2 `S.union` fv1 `S.union` M.keysSet s1
>           y   = newId vs

>           s   = singleSub x (var y) `comp` s1 `comp` s2
>           s'  = M.filterWithKey (\v _ -> v == x || v `elem` fv) s
>           s2' = M.filterWithKey (\v _ -> v `elem` freeVars b) s2
>           s1s2 = s1 `comp` s2
>           s1s2' = M.filterWithKey (\v _ -> v `elem` fv) s1s2

> instance (NFData x, NFData a) => NFData (Bind x a) where
>     rnf (Bind s f b x a) = rnf s `seq` rnf f `seq` rnf b `seq` rnf x `seq` rnf a

-------------------------------------------------------------------

> type Sub = M.Map
 
> emptySub :: Sub v e
> emptySub = M.empty

> singleSub :: v -> e -> Sub v e
> singleSub = M.singleton

> comp :: (Subst v e e) => Sub v e -> Sub v e -> Sub v e
> comp s1 s2
>   | null s1   = s2
>   | null s2   = s1
>  -- union is left biased. We want the value from s1 if there is also a definition in s2
>   | otherwise = subst s2 s1 <> s2


> instance FreeVars v e => FreeVars v (Sub v e) where
>   freeVars    = foldMap freeVars
>   boundVars   = foldMap boundVars

> instance Subst v a e => Subst v a (Sub v e) where
>   subst s2 s1 = M.map (subst s2) s1


-------------------------------------------------------------------

> instance Atom v => FreeVars v v where
>    freeVars = S.singleton
>    boundVars _ = S.empty


-------------------------------------------------------------------

> data Exp v = Var !v | Lam !(Bind v (Exp v)) | App !(Exp v) !(Exp v)
>
> instance NFData v => NFData (Exp v) where
>    rnf (Var i) = rnf i
>    rnf (Lam d) = rnf d
>    rnf (App a b) = rnf a `seq` rnf b


> instance Atom v => Var v (Exp v) where
>    var = Var

> instance Atom v => FreeVars v (Exp v) where
>   freeVars (Var v)   = freeVars v
>   freeVars (Lam b)   = freeVars b
>   freeVars (App f a) = freeVars f `S.union` freeVars a

>   boundVars (Var v)   = S.empty
>   boundVars (Lam b)   = boundVars b
>   boundVars (App f a) = boundVars f `S.union` boundVars a



> instance Atom v => Subst v (Exp v) (Exp v) where
>   subst s (Var x)    = M.findWithDefault (Var x) x s
>   subst s (Lam b)    = Lam (subst s b)
>   subst s (App f a)  = App (subst s f) (subst s a) 

-------------------------------------------------------------------

> aeq :: Atom v => LC.LC v -> LC.LC v -> Bool
> aeq x y = aeqd (toExp x) (toExp y)


> nf :: Atom v => LC.LC v -> LC.LC v
> nf = fromExp . nfd . toExp

Alpha-equivalence

> aeqBind :: Atom v => Bind v (Exp v) -> Bind v (Exp v) -> Bool
> aeqBind (Bind s1 _f1 _bv1 x1 b1) e2@(Bind s2 _f2 _bv2 x2 b2)
>   | x1 == x2 = aeqd (subst s1 b1) (subst s2 b2)
>   | x1 `elem` freeVars e2 = False
>   | otherwise = aeqd (subst s1 b1) (subst (singleSub x2 (Var x1) `comp` s2) b2)

> aeqd :: Atom v =>Exp v -> Exp v -> Bool
> aeqd (Var v1)    (Var v2)    = v1 == v2
> aeqd (Lam e1)    (Lam e2)    = aeqBind e1 e2
> aeqd (App a1 a2) (App b1 b2) = aeqd a1 b1 && aeqd a2 b2
> aeqd _ _ = False


Computing the normal form proceeds as usual. 

> nfd :: Atom v => Exp v -> Exp v
> nfd e@(Var _) = e
> nfd (Lam b) = 
>   --trace ("nf of " ++ show (Lam b) ++ " is " ++ show b') $
>   b'
>      where (x,a) = unbind b
>            b'    = Lam (bind x (nfd a))
> nfd (App f a) =
>     -- trace ("whnf " ++ show f ++ " is " ++ show (whnf f)) $
>     case whnf f of
>         Lam b -> nfd (instantiate b a)
>         f' -> App (nfd f') (nfd a)

Compute the weak head normal form. 

> whnf :: Atom v => Exp v -> Exp v
> whnf e@(Var _) = e
> whnf e@(Lam _) = e
> whnf (App f a) =
>     case whnf f of
>         Lam b -> whnf (instantiate b a)
>         f' -> App f' a

---------------------------------------------------------

> nfi :: Atom v => Int -> Exp v -> Maybe (Exp v)
> nfi 0 _e = Nothing
> nfi _n e@(Var _) = return  e
> nfi n (Lam b) = Lam . bind x <$> nfi (n-1) a where (x,a) = unbind b
> nfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam b -> nfi (n-1) (instantiate b a)
>         _ -> App <$> nfi (n-1) f' <*> nfi (n-1) a

> whnfi :: Atom v => Int -> Exp v -> Maybe (Exp v)
> whnfi 0 _e = Nothing 
> whnfi _n e@(Var _) = return e
> whnfi _n e@(Lam _) = return e
> whnfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam b -> whnfi (n - 1) (instantiate b a)
>         _ -> return $ App f' a

---------------------------------------------------------

> toExp :: Atom v => LC.LC v -> Exp v
> toExp = to
>   where to (LC.Var v)   = Var v
>         to (LC.Lam x b) = Lam (bind x (to b))
>         to (LC.App f a) = App (to f) (to a)

Convert back from deBruijn to the LC type.

> fromExp :: Atom v => Exp v -> LC.LC v
> fromExp = from 
>   where from (Var i)   = LC.Var i
>         from (Lam b)   = LC.Lam x (from a)
>             where (x,a) = unbind b
>         from (App f a) = LC.App (from f) (from a)

---------------------------------------------------------

> instance (Atom v, Show v) => Show (Exp v) where
>     show = renderStyle style . ppExp 0


> ppExp :: (Atom v, Show v) => Int -> Exp v -> Doc
> ppExp _ (Var v)   = text $ show v
> ppExp p (Lam b)   = pparens (p>0) $ text "\\" <> text (show x) <> text "."
>                                       <> ppExp 0 a where (x,a) = unbind b
> ppExp p (App f a) = pparens (p>1) $ ppExp 1 f <+> ppExp 2 a


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
