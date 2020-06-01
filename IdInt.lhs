A fast type of identifiers, Ints, for $\lambda$-expressions.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module IdInt(IdInt(..), firstBoundId, toIdInt, genScoped, shrinkScoped) where
> import qualified Data.Map as M
> import Control.Monad.State
> import GHC.Generics
> import Control.DeepSeq
> import Lambda
> import Test.QuickCheck

An IdInt is just another name for an Int.

> newtype IdInt = IdInt Int
>     deriving (Eq, Ord, Generic)
>
> instance NFData IdInt
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
>   where fvmap = Prelude.foldr (\ (v, i) m -> M.insert v (IdInt i) m) M.empty
>                               (zip (freeVars e) [1..])

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
> conv (Var v)   = Var <$> convVar v
> conv (Lam v e) = Lam <$> convVar v <*> conv e
> conv (App f a) = App <$> conv f    <*> conv a

> instance Arbitrary IdInt where
>    arbitrary = IdInt <$> arbitrarySizedNatural
>    shrink (IdInt 0) = []
>    shrink (IdInt n) = [IdInt (n-1)]



> genScoped :: Gen (LC IdInt)
> genScoped = lams <$> sized (gen vars) where
>     vars :: [IdInt]
>     vars = take 5 [firstBoundId ..]
> 
>     lams :: LC IdInt -> LC IdInt
>     lams body = foldr Lam body vars
> 
>     gen :: [IdInt] -> Int -> Gen (LC IdInt)
>     gen xs n | not (null xs) && n <= 1 = var
>              | null xs                 = oneof [lam,app]
>              | otherwise               = oneof [var,lam,lam,app]
>        where
>           n'  = n `div` 2
>           lam = do let x = succ (head xs)
>                    Lam x <$> gen (x:xs) n'
>           app = App <$> gen xs n' <*> gen xs n'
>           var = Var <$> elements xs
>     

> shrinkScoped :: LC IdInt -> [LC IdInt]
> shrinkScoped e = lams <$> s (peel e) where
>    vars = take 5 [firstBoundId ..]
>    lams :: LC IdInt -> LC IdInt
> 
>    lams body = foldr Lam body vars
> 
>    peel (Lam _ (Lam _ (Lam _ (Lam _ (Lam _ e1))))) = e1
> 
>    s (Lam v e) = [e | v `notElem` freeVars e ]
>    s (Var _x)  = []
>    s (App e1 e2) = e1 : e2 : [App e1 e2' | e2' <- s e2] ++ [App e1' e2 | e1' <- s e1]
