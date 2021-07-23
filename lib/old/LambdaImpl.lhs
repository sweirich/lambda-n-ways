
The Lambda module implements a simple abstract syntax for
$\lambda$-calculus together with a parser and a printer for it.
It also exports a simple type of identifiers that parse and
print in a nice way.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TupleSections #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE UndecidableInstances #-}

> module LambdaImpl(LC(..), Impl(..), allVars, Id(..), genScoped, shrinkScoped,
>      prop_roundTrip, genScopedLam, maxBindingDepth, depth) where
> import Data.List(union, (\\))
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.ParserCombinators.ReadP
> import GHC.Generics
> import Control.DeepSeq
> import Control.Monad.State

> import qualified Data.Map as M
> import Data.Map (Map)
>
> import Test.QuickCheck
> import Data.Kind (Type)

> import Util.IdInt

> class (Arbitrary v, Ord v, NFData v, Read v, Show v)
>   => Impl v where
>    type Bind v  :: Type -> Type
>    type Subst v :: Type -> Type 
>    freeVars     :: LC v -> [v]
>    aeq          :: LC v -> LC v -> Bool 
>    bind         :: v -> LC v -> Bind v (LC v)
>    unbind       :: Bind v (LC v) -> (v, LC v)
>    instantiate  :: Bind v (LC v) -> LC v -> LC v
>    subst        :: Subst v (LC v) -> LC v -> LC v 
>    toLC         :: LC v -> LC IdInt
>    fromLC       :: LC IdInt -> LC v

The LC type of $\lambda$ term is parametrized over the type of the variables,
which also specifies the implementation.

It has constructors for variables, $\lambda$-abstraction, and application.

> data LC v = Var v | Lam (Bind v (LC v)) | App (LC v) (LC v)
>    deriving (Generic)
>
> instance (NFData a, NFData (Bind a (LC a))) => NFData (LC a)

> instance Impl v => Eq (LC v) where
>   (==) = aeq

> lam :: Impl v => v -> LC v -> LC v
> lam v e = Lam (bind v e)

------------------------------------------------------------------------


> instance Impl IdInt where
>   type Bind IdInt = (,) IdInt
>   type Subst IdInt = Map IdInt

>   freeVars :: LC IdInt -> [IdInt]
>   freeVars (Var v) = [v]
>   freeVars (Lam b) = freeVars e \\ [v]  
>      where (v,e) = unbind b
>   freeVars (App f a) = freeVars f `union` freeVars a

>   aeq :: LC IdInt -> LC IdInt -> Bool
>   aeq = aeqd where
>     aeqd (Var v1) (Var v2) = v1 == v2
>     aeqd (Lam (v1, e1)) (Lam (v2, e2))
>       | v1 == v2 = aeqd e1 e2
>       | v1 `elem` freeVars (Lam (v2, e2))  = False
>       | otherwise = aeqd e1 (applyPermLC p e2) where
>          p = (extendPerm emptyPerm v1 v2)
>     aeqd (App a1 a2) (App b1 b2) =
>       aeqd a1 b1 && aeqd a2 b2
>     aeqd _ _ = False
>   bind = (,)
>   unbind = id
>   toLC = id
>   fromLC = id
>   subst = substDefault
>   instantiate (v, a) b = subst (M.singleton v b) a



Substitution has only one interesting case, the abstraction.
For abstraction there are three cases:
if the bound variable, {\tt v}, is one of the variables we
are replacing then we are done,
if the bound variable is in set set of free variables
of the substituted expression then there would be
an accidental capture and we rename it,
otherwise the substitution just continues.

How should the new variable be picked when doing the
renaming?  The new variable must not be in the set of
free variables of {\tt s} since this would case another
accidental capture, nor must it be among the free variables
of {\tt e'} since this could cause another accidental
capture.  Conservatively, we avoid all variables occuring
in the original {\tt b} to fulfill the second requirement.

> substDefault :: (Nominal v, Impl v) => Map v (LC v) -> LC v -> LC v
> substDefault ss b = sub vs0 b
>  where 
>        sub _ e@(Var v) | v `M.member` ss = ss M.! v
>                        | otherwise = e
>        sub vs e@(Lam b) | v `M.member` ss = e
>                         | v `elem` fvs = lam v' (sub (v':vs) e'')
>                         | otherwise = lam v (sub (v:vs) e')
>                             where 
>                               (v, e') = unbind b
>                               v' = newId vs
>                               e'' = substDefault (M.singleton v (Var v')) e'
>        sub vs (App f a) = App (sub vs f) (sub vs a)
>        
>        fvs = foldMap freeVars ss
>        vs0 = fvs `union` allVars b
>               `union` M.keys ss -- make sure we don't rename v' to variable we are sub'ing for

(Note: this code was updated according to Kmett's blog post
 https://www.schoolofhaskell.com/user/edwardk/bound.)

Get a variable which is not in the given set.
Do this simply by generating all variables and picking the
first not in the given set.

Any variable type can be converted to IdInt if we can just build
a table of them.
The conversion assigns a different Int to each different original
identifier.

> toIdInt :: (Impl v) => LC v -> LC IdInt
> toIdInt e = evalState (conv e) (0, fvmap)
>   where fvmap = Prelude.foldr (\ (v, i) m -> M.insert v (IdInt i) m) M.empty
>                               (zip (freeVars e) [1..])

> conv :: (Impl v) => LC v -> FreshM v (LC IdInt)
> conv (Var v)   = Var <$> convVar v
> conv (Lam b)   = Lam <$> (bind <$> convVar v <*> conv e)
>   where (v,e)  = unbind b
> conv (App f a) = App <$> conv f    <*> conv a

Compute *all* variables in an expression.

> allVars :: (Impl v) => LC v -> [v]
> allVars (Var v)   = [v]
> allVars (Lam b)   = allVars e where (_,e) = unbind b
> allVars (App f a) = allVars f `union` allVars a

For alpha-equivalence, we can optimize the case where the binding variable is
the same. However, if it is not, we need to check to see if the left binding
variable is free in the body of the right Lam. If so, then the terms cannot be
alpha-equal. Otherwise, we can remember that the right one matches up with the
left.

> type Perm v = (M.Map v v, M.Map v v)
> 
> applyPerm :: Ord v => Perm v -> v -> v
> applyPerm (m1,m2) x
>   | Just y <- M.lookup x m1 =  y
>   | Just y <- M.lookup x m2 =  y
>   | otherwise = x
>
> applyPermLC :: Perm IdInt -> LC IdInt -> LC IdInt
> applyPermLC m (Var x)   = Var (applyPerm m x)
> applyPermLC m (Lam (x, e)) = Lam (applyPerm m x, applyPermLC m e)
> applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)

> emptyPerm :: Perm v
> emptyPerm = (M.empty, M.empty)
> 
> extendPerm :: Ord v => Perm v -> v -> v -> Perm v
> extendPerm (m1, m2) x y = (M.insert x y m1, M.insert y x m2)

> lookupVar :: Ord v => Map v v -> v -> v
> lookupVar m x = M.findWithDefault x x m 

---------------------------- Read/Show -------------------------------------

The Read instance for the LC type reads $\lambda$ term with the normal
syntax.

> instance (Impl v) => Read (LC v) where
>     readsPrec _ = readP_to_S pLC

A ReadP parser for $\lambda$-expressions.

> pLC, pLCAtom, pLCVar, pLCLam, pLCApp :: (Impl v) => ReadP (LC v)
> pLC = pLCLam +++ pLCApp +++ pLCLet
>
> pLCVar = do
>     v <- pVar
>     return $ Var v
>
> pLCLam = do
>     _ <- schar '\\'
>     v <- pVar
>     _ <- schar '.'
>     e <- pLC
>     return $ Lam (bind v e)
>
> pLCApp = do
>     es <- many1 pLCAtom
>     return $ foldl1 App es
>
> pLCAtom = pLCVar +++ (do _ <- schar '('; e <- pLC; _ <- schar ')'; return e)

To make expressions a little easier to read we also allow let expression
as a syntactic sugar for $\lambda$ and application.

> pLCLet :: (Impl v) => ReadP (LC v)
> pLCLet = do
>     let lcLet (x,e) b = App (Lam (bind x b)) e
>         pDef = do
>           v <- pVar
>           _ <- schar '='
>           e <- pLC
>           return (v, e)
>     _ <- sstring "let"
>     bs <- sepBy pDef (schar ';')
>     _ <- sstring "in"
>     e <- pLC
>     return $ foldr lcLet e bs

>
> schar :: Char -> ReadP Char
> schar c = do skipSpaces; char c
>
> sstring :: String -> ReadP String
> sstring c = do skipSpaces; string c
>
> pVar :: (Read v) => ReadP v
> pVar = do skipSpaces; readS_to_P (readsPrec 9)

Pretty print $\lambda$-expressions when shown.

> instance (Impl v) => Show (LC v) where
>     show = renderStyle style . ppLC 0
>
> ppLC :: (Impl v) => Int -> LC v -> Doc
> ppLC _ (Var v)   = text $ show v
> ppLC p (Lam b)   = pparens (p>0) $ text ("\\" ++ show v ++ ".") PP.<> ppLC 0 e
>   where (v,e) = unbind b
> ppLC p (App f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d

-----------------------------------------------------------------------------------------

The Id type of identifiers.

> newtype Id = Id String
>     deriving (Eq, Ord)

Identifiers print and parse without any adornment.

> instance Show Id where
>     show (Id i) = i

> instance Read Id where
>     readsPrec _ s =
>         case span isAlphaNum s of
>         ("", _) -> []
>         (i, s') -> [(Id i, s')]

> instance Arbitrary Id where
>    arbitrary = Id  <$> genSafeString

> genSafeChar :: Gen Char
> genSafeChar = elements ['a'..'z']

> genSafeString :: Gen String
> genSafeString = listOf1 genSafeChar

Round trip property for parsing / pp

> prop_roundTrip :: LC IdInt -> Bool
> prop_roundTrip x = read (show x) == x

> ----------------------- Arbitrary instances -----------------------------------

Generate an arbitrary *well-scoped* lambda calculus term

> instance Impl v => Arbitrary (LC v) where
>   arbitrary = sized gen where
>     
>     gen n | n <= 1    = Var <$> arbitrary
>           | otherwise =
>               frequency [(1, Var <$> arbitrary)
>                         ,(1, Lam <$> (bind <$> arbitrary <*> gen (n `div` 2)))
>                         ,(1, App <$> gen (n `div` 2) <*> gen (n `div` 2))]
> 
>   shrink (Var v)   = [ Var n | n <- shrink v ]
>   shrink (Lam b) = e : [ Lam (bind n e) | n <- shrink v ] 
>          ++ [Lam (bind v e') | e' <- shrink e]
>     where (v,e) = unbind b
>   shrink (App e1 e2) = [ App e1' e1 | e1' <- shrink e1] ++
>                        [ App e1 e2' | e2' <- shrink e2] 



Generate an arbitrary *well-scoped* lambda calculus term


> genScoped :: forall v. (Enum v, Impl v) => Gen (LC v)
> genScoped = lams <$> sized (gen vars) where
> 
>     vars :: [v]
>     vars = take 5 [(toEnum 0) ..]
> 
>     lams :: LC v -> LC v
>     lams body = foldr lam body vars
> 
>     gen :: [v] -> Int -> Gen (LC v)
>     gen xs n | not (null xs) && n <= 1 = var
>              | null xs                 = oneof [lam,app]
>              | otherwise               = oneof [var,lam,app]
>        where
>           n'  = n `div` 2
>           lam = do let x = succ (head xs)
>                    Lam <$> (bind x <$> gen (x:xs) n')
>           app = App <$> gen xs n' <*> gen xs n'
>           var = Var <$> elements xs
>     

> shrinkScoped :: forall v. (Enum v, Impl v) => LC v -> [LC v]
> shrinkScoped e = lams <$> s (peel e) where
>    vars = take 5 [(toEnum 0) ..]
> 
>    lams :: Impl v => LC v -> LC v
>    lams body = foldr (\v e -> Lam (bind v e)) body vars
> 
>    peel (Lam b1) 
>     | (_, Lam b2) <- unbind b1 
>     , (_, Lam b3) <- unbind b2
>     , (_, Lam b4) <- unbind b3
>     , (_, Lam b5) <- unbind b4
>     , (_, e1) <- unbind b5
>     = e1
>    peel _ = error "start with 5 lambda-bound variables"
>
>    s :: Impl v => LC v -> [LC v]
>    s (Lam b) = [e | v `notElem` freeVars e ] where (v,e) = unbind b
>    s (Var _x)  = []
>    s (App e1 e2) = e1 : e2 : [App e1 e2' | e2' <- s e2] ++ [App e1' e2 | e1' <- s e1]


Lambda nodes don't decrease the size and the lam constructor is chosen more frequently.
Will produce terms with a bigger nesting depth and more lambda reductions

> genScopedLam :: forall v. (Impl v, Enum v, Arbitrary v) => Gen (LC v)
> genScopedLam = lams <$> sized (gen vars) where
> 
>     vars :: [v]
>     vars = take 5 [(toEnum 0) ..]
> 
>     lams :: LC v -> LC v
>     lams body = foldr lam body vars
> 
>     gen :: [v] -> Int -> Gen (LC v)
>     gen xs n | not (null xs) && n <= 1 = var
>              | null xs                 = oneof [lam,app]
>              | otherwise               = oneof [var,lam,lam,lam,app]
>        where
>           n'  = n `div` 2
>           lam = do let x = succ (head xs)
>                    Lam <$> (bind x <$> gen (x:xs) n)
>           app = App <$> gen xs n' <*> gen xs n'
>           var = Var <$> elements xs


> maxBindingDepth :: Impl v => LC v -> Int
> maxBindingDepth = go where
>  go (Var _v) = 0
>  go (Lam b) = 1 + go t where (_v, t) = unbind b
>  go (App t s)  = max (go t) (go s)

> depth :: Impl v => LC v -> Int
> depth = go where
>  go (Var _v) = 0
>  go (Lam b) = 1 + go t where (_v, t) = unbind b
>  go (App t s) = 1 + max (go t) (go s)
