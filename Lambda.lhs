The Lambda module implements a simple abstract syntax for
$\lambda$-calculus together with a parser and a printer for it.
It also exports a simple type if identifiers that parse and
print in a nice way.

> module Lambda(LC(..), freeVars, allVars, Id(..)) where
> import Data.List(span, union, (\\))
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<>), (<+>), parens)
> import Text.ParserCombinators.ReadP

The LC type of $\lambda$ term is parametrized over the type of the variables.
It has constructors for variables, $\lambda$-abstraction, and application.

> data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
>    deriving (Eq)

Compute the free variables of an expression.

> freeVars :: (Eq v) => LC v -> [v]
> freeVars (Var v) = [v]
> freeVars (Lam v e) = freeVars e \\ [v]
> freeVars (App f a) = freeVars f `union` freeVars a

Compute all variables in an expression.

> allVars :: (Eq v) => LC v -> [v]
> allVars (Var v) = [v]
> allVars (Lam _ e) = allVars e
> allVars (App f a) = allVars f `union` allVars a

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
>     schar '\\'
>     v <- pVar
>     schar '.'
>     e <- pLC
>     return $ Lam v e
>
> pLCApp = do
>     es <- many1 pLCAtom
>     return $ foldl1 App es
>
> pLCAtom = pLCVar +++ (do schar '('; e <- pLC; schar ')'; return e)

To make expressions a little easier to read we also allow let expression
as a syntactic sugar for $\lambda$ and application.

> pLCLet :: (Read v) => ReadP (LC v)
> pLCLet = do
>     let lcLet (x,e) b = App (Lam x b) e
>         pDef = do
>           v <- pVar
>           schar '='
>           e <- pLC
>           return (v, e)
>     sstring "let"
>     bs <- sepBy pDef (schar ';')
>     sstring "in"
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
> ppLC _ (Var v) = text $ show v
> ppLC p (Lam v e) = pparens (p>0) $ text ("\\" ++ show v ++ ".") <> ppLC 0 e
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

