A fast type of identifiers, Ints, for $\lambda$-expressions.

> module IdInt(IdInt(..), firstBoundId, toIdInt) where
> import Data.Map as M
> import Control.Monad.State
> import Lambda

An IdInt is just another name for an Int.

> newtype IdInt = IdInt Int
>     deriving (Eq, Ord)
>
> firstBoundId :: IdInt
> firstBoundId = IdInt 0

It is handly to make IdInt enumerable.

> instance Enum IdInt where
>     toEnum i = IdInt i
>     fromEnum (IdInt i) = i

We show IdInts so they look like variables.  Negative numbers
are free variables.

> instance Show IdInt where
>    show (IdInt i) = if i < 0 then "f" ++ show (-i) else "x" ++ show i

Any variable type can be converted to IdInt if we can just build
a table of them.
The conversion assigns a different Int to each different original
identifier.
Free variables in the expression are translated into negative numbers
so they are easily distinguished later.

> toIdInt :: (Ord v) => LC v -> LC IdInt
> toIdInt e = evalState (conv e) (0, fvmap)
>   where fvmap = foldr (\ (v, i) m -> insert v (IdInt (-i)) m) empty
>                       (zip (freeVars e) [1..])

The state monad has the next unused Int and a mapping of identifiers to IdInt.

> type M v a = State (Int, Map v IdInt) a

The only operation we do in the monad is to convert a variable.
If the variable is in the map the use it, otherwise add it.

> convVar :: (Ord v) => v -> M v IdInt
> convVar v = do
>    (i, m) <- get
>    case M.lookup v m of
>        Nothing -> do
>            let ii = IdInt i
>            put (i+1, insert v ii m)
>            return ii
>        Just ii -> return ii

> conv :: (Ord v) => LC v -> M v (LC IdInt)
> conv (Var v) = liftM Var (convVar v)
> conv (Lam v e) = liftM2 Lam (convVar v) (conv e)
> conv (App f a) = liftM2 App (conv f) (conv a)

