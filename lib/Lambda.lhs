
The Lambda module implements a simple abstract syntax for
$\lambda$-calculus together with a parser and a printer for it.
It also exports a simple type of identifiers that parse and
print in a nice way.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Lambda(LC(..), freeVars, allVars, Id(..), aeq, genScoped, shrinkScoped,
> prop_roundTrip, genScopedLam, maxBindingDepth, depth) where
> import Data.List(union, (\\))
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.ParserCombinators.ReadP
> import GHC.Generics
> import Control.DeepSeq

> import qualified Data.Map as M
> import Data.Map (Map)
>
> import Test.QuickCheck


The LC type of $\lambda$ term is parametrized over the type of the variables.
It has constructors for variables, $\lambda$-abstraction, and application.

> data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
>    deriving (Eq, Generic)
>
> instance NFData a => NFData (LC a)

Compute the free variables of an expression.

> freeVars :: (Eq v) => LC v -> [v]
> freeVars (Var v)   = [v]
> freeVars (Lam v e) = freeVars e \\ [v]
> freeVars (App f a) = freeVars f `union` freeVars a

Compute *all* variables in an expression.

> allVars :: (Eq v) => LC v -> [v]
> allVars (Var v) = [v]
> allVars (Lam _ e) = allVars e
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
> applyPermLC :: Ord v => Perm v -> LC v -> LC v
> applyPermLC m (Var x)   = Var (applyPerm m x)
> applyPermLC m (Lam x e) = Lam (applyPerm m x) (applyPermLC m e)
> applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)

> emptyPerm :: Perm v
> emptyPerm = (M.empty, M.empty)
> 
> extendPerm :: Ord v => Perm v -> v -> v -> Perm v
> extendPerm (m1, m2) x y = (M.insert x y m1, M.insert y x m2)

> lookupVar :: Ord v => Map v v -> v -> v
> lookupVar m x = M.findWithDefault x x m 

> -- inefficient version
> aeq :: Ord v => LC v -> LC v -> Bool
> aeq = aeqd where
>   aeqd (Var v1) (Var v2) = v1 == v2
>   aeqd (Lam v1 e1) (Lam v2 e2)
>     | v1 == v2 = aeqd e1 e2
>     | v1 `elem` freeVars (Lam v2 e2)  = False
>     | otherwise = aeqd e1 (applyPermLC p e2) where
>          p = (extendPerm emptyPerm v1 v2)
>   aeqd (App a1 a2) (App b1 b2) =
>     aeqd a1 b1 && aeqd a2 b2
>   aeqd _ _ = False


---------------------------- Read/Show -------------------------------------

The Read instance for the LC type reads $\lambda$ term with the normal
syntax.

> instance (Read v) => Read (LC v) where
>     readsPrec _ = readP_to_S pLC

A ReadP parser for $\lambda$-expressions.

> pLC, pLCAtom, pLCVar, pLCLam, pLCApp :: (Read v) => ReadP (LC v)
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
>     return $ Lam v e
>
> pLCApp = do
>     es <- many1 pLCAtom
>     return $ foldl1 App es
>
> pLCAtom = pLCVar +++ (do _ <- schar '('; e <- pLC; _ <- schar ')'; return e)

To make expressions a little easier to read we also allow let expression
as a syntactic sugar for $\lambda$ and application.

> pLCLet :: (Read v) => ReadP (LC v)
> pLCLet = do
>     let lcLet (x,e) b = App (Lam x b) e
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

> instance (Show v) => Show (LC v) where
>     show = renderStyle style . ppLC 0
>
> ppLC :: (Show v) => Int -> LC v -> Doc
> ppLC _ (Var v)   = text $ show v
> ppLC p (Lam v e) = pparens (p>0) $ text ("\\" ++ show v ++ ".") PP.<> ppLC 0 e
> ppLC p (App f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d

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

> prop_roundTrip :: LC Id -> Bool
> prop_roundTrip x = read (show x) == x

> ----------------------- Arbitrary instances -----------------------------------

Generate an arbitrary *well-scoped* lambda calculus term

> instance Arbitrary v => Arbitrary (LC v) where
>   arbitrary = sized gen where
>     
>     gen n | n <= 1    = Var <$> arbitrary
>           | otherwise =
>               frequency [(1, Var <$> arbitrary)
>                         ,(1, Lam <$> arbitrary <*> gen (n `div` 2))
>                         ,(1, App <$> gen (n `div` 2) <*> gen (n `div` 2))]
> 
>   shrink (Var v)   = [ Var n | n <- shrink v ]
>   shrink (Lam v e) = e : [ Lam n e | n <- shrink v ] ++ [Lam v e' | e' <- shrink e]
>   shrink (App e1 e2) = [ App e1' e1 | e1' <- shrink e1] ++
>                        [ App e1 e2' | e2' <- shrink e2] 



Generate an arbitrary *well-scoped* lambda calculus term


> genScoped :: forall v. (Enum v, Arbitrary v) => Gen (LC v)
> genScoped = lams <$> sized (gen vars) where
> 
>     vars :: [v]
>     vars = take 5 [(toEnum 0) ..]
> 
>     lams :: LC v -> LC v
>     lams body = foldr Lam body vars
> 
>     gen :: [v] -> Int -> Gen (LC v)
>     gen xs n | not (null xs) && n <= 1 = var
>              | null xs                 = oneof [lam,app]
>              | otherwise               = oneof [var,lam,app]
>        where
>           n'  = n `div` 2
>           lam = do let x = succ (head xs)
>                    Lam x <$> gen (x:xs) n'
>           app = App <$> gen xs n' <*> gen xs n'
>           var = Var <$> elements xs
>     

> shrinkScoped :: forall v. (Enum v, Eq v) => LC v -> [LC v]
> shrinkScoped e = lams <$> s (peel e) where
>    vars = take 5 [(toEnum 0) ..]
> 
>    lams :: LC v -> LC v
>    lams body = foldr Lam body vars
> 
>    peel (Lam _ (Lam _ (Lam _ (Lam _ (Lam _ e1))))) = e1
>    peel _ = error "start with 5 lambda-bound variables"
>
>    s :: LC v -> [LC v]
>    s (Lam v e) = [e | v `notElem` freeVars e ]
>    s (Var _x)  = []
>    s (App e1 e2) = e1 : e2 : [App e1 e2' | e2' <- s e2] ++ [App e1' e2 | e1' <- s e1]


Lambda nodes don't decrease the size and the lam constructor is chosen more frequently.
Will produce terms with a bigger nesting depth and more lambda reductions

> genScopedLam :: forall v. (Enum v, Arbitrary v) => Gen (LC v)
> genScopedLam = lams <$> sized (gen vars) where
> 
>     vars :: [v]
>     vars = take 5 [(toEnum 0) ..]
> 
>     lams :: LC v -> LC v
>     lams body = foldr Lam body vars
> 
>     gen :: [v] -> Int -> Gen (LC v)
>     gen xs n | not (null xs) && n <= 1 = var
>              | null xs                 = oneof [lam,app]
>              | otherwise               = oneof [var,lam,lam,lam,app]
>        where
>           n'  = n `div` 2
>           lam = do let x = succ (head xs)
>                    Lam x <$> gen (x:xs) n
>           app = App <$> gen xs n' <*> gen xs n'
>           var = Var <$> elements xs


> maxBindingDepth :: LC v -> Int
> maxBindingDepth = go where
>  go (Var _v) = 0
>  go (Lam _v t) = 1 + go t
>  go (App t s) = max (go t) (go s)

> depth :: LC v -> Int
> depth = go where
>  go (Var _v) = 0
>  go (Lam _v t) = 1 + go t
>  go (App t s) = 1 + max (go t) (go s)
