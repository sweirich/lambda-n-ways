A fast type of identifiers, Ints, for lambda expressions.

> module IdInt(IdInt(..), toIdInt, freeVars, allVars) where
> import Data.List
> import qualified Data.Map as M
> import Control.Monad.State
> import Lambda

An IdInt is just anothet name for an Int.

> newtype IdInt = IdInt Int
>     deriving (Eq, Ord)

We show IdInts so they look like variables

> instance Show IdInt where
>    show (IdInt i) = "x" ++ show i

Any variable type can be converted to IdInt if we can just build
a table of them.
The conversion assign a different Int to each different original
identifier.

> toIdInt :: (Ord v) => LC v -> LC IdInt
> toIdInt e = evalState (conv e) (0, M.empty)

The state monad has the next unused Int and a mapping of identifiers to IdInt.

> type M v a = State (Int, M.Map v IdInt) a

The only operation we do in the monad is to convert a variable.
If the variable is in the map the use it, otherwise add it.

> convVar :: (Ord v) => v -> M v IdInt
> convVar v = do
>    (i, m) <- get
>    case M.lookup v m of
>        Nothing -> do
>            let ii = IdInt i
>            put (i+1, M.insert v ii m)
>            return ii
>        Just ii -> return ii

> conv :: (Ord v) => LC v -> M v (LC IdInt)
> conv (Var v) = liftM Var (convVar v)
> conv (Lam v e) = liftM2 Lam (convVar v) (conv e)
> conv (App f a) = liftM2 App (conv f) (conv a)

Compute the free variables of an expression.

> freeVars :: LC IdInt -> [IdInt]
> freeVars (Var v) = [v]
> freeVars (Lam v e) = freeVars e \\ [v]
> freeVars (App f a) = freeVars f `union` freeVars a

Compute all variables in an expression.

> allVars :: LC IdInt -> [IdInt]
> allVars (Var v) = [v]
> allVars (Lam _ e) = allVars e
> allVars (App f a) = allVars f `union` allVars a

