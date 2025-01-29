The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Lennart.Unique(impl) where
> import Util.Syntax.Lambda (LC(..))
> import Data.List(union)
> import qualified Util.Syntax.Lambda as LC
> import qualified Data.Map as M
> import Control.Monad.State
> import Util.IdInt hiding (newId)
> import Data.Maybe (fromMaybe)
> import Control.DeepSeq
> import Control.Monad
> import Test.QuickCheck
> import qualified Util.Stats as Stats


> import Util.Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Lennart.Unique"
>           , impl_fromLC = toUnique
>           , impl_toLC   = id
>           , impl_nf     = nf
>           , impl_nfi    = nfi
>           , impl_aeq    = Lennart.Unique.aeq
>        }


Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.

> nf :: LC IdInt -> LC IdInt
> nf e = evalState (nf' e') i
>   where (e', (i,_)) = runState (unique e) (firstBoundId, M.empty)


Our state monad. 

> type N a = State IdInt a

> nf' :: LC IdInt -> N (LC IdInt)
> nf' e@(Var _) = return e
> nf' (Lam x e) = Lam x <$> nf' e
> nf' (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= nf'
>         _ -> App <$> nf' f' <*> nf' a

Compute the weak head normal form.

> whnf :: LC IdInt -> N (LC IdInt)
> whnf e@(Var _) = return e
> whnf e@(Lam _ _) = return e
> whnf (App f a) = do
>     f' <- whnf f
>     case f' of
>         (Lam x b) -> subst x a b >>= whnf
>         _ -> return $ App f' a

Fueled version:

> type NM a = StateT IdInt Stats.M a

> nfi :: Int -> LC IdInt -> Stats.M (LC IdInt)
> nfi x e = fst <$> result where
>     result = runStateT (nfi' x e) (initState e)

> nfi' :: Int -> LC IdInt -> NM  (LC IdInt)
> nfi' 0 _ = lift Stats.done
> nfi' _i e@(Var _) = return e
> nfi' i (Lam x e) = Lam x <$> nfi' (i-1) e
> nfi' i (App f a) = do
>     f' <- whnfi (i-1) f
>     case f' of
>         Lam x b -> do
>               lift Stats.count
>               t <- subst x a b
>               nfi' (i-1) t
>         _ -> App <$> nfi' (i-1) f' <*> nfi' (i-1) a

Compute the weak head normal form.

> whnfi :: Int -> LC IdInt -> NM (LC IdInt)
> whnfi 0 _ = lift Stats.done
> whnfi _ e@(Var _) = return e
> whnfi _ e@(Lam _ _) = return e
> whnfi i (App f a) = do
>     f' <- whnfi (i-1) f
>     case f' of
>         (Lam x b) -> lift Stats.count >> subst x a b >>= whnfi (i-1)
>         _ -> return $ App f' a

Substitution proceeds by cloning the term that is inserted
at every place it is put.

(TODO: No need to clone $\lambda$-free terms.)

> subst :: forall m. (MonadState IdInt m) 
>       => IdInt -> LC IdInt -> LC IdInt -> m (LC IdInt)
> subst x s = sub
>  where 
>        sub e@(Var v) | v == x    = clone M.empty s
>                      | otherwise = return e
>        sub (Lam v e) = Lam v <$> sub e
>        sub (App f a) = App <$> sub f <*> sub a
>
>        clone :: M.Map IdInt IdInt -> LC IdInt -> m (LC IdInt)
>        clone m e@(Var v) = return $ maybe e Var (M.lookup v m)
>        clone m (Lam v e) = do v' <- newVar; Lam v' <$> clone (M.insert v v' m) e
>        clone m (App f a) = App <$> clone m f <*> clone m a
>


Create a fresh variable.

> newVar :: (MonadState IdInt m) => m IdInt
> newVar = do
>     i <- get
>     put (succ i)
>     return i

Do the actual translation of the term to unique variables.
We keep mapping of old variable names to new variable name.
Free variables are just left alone since they are already
uniquely named.

> type U a  = State (IdInt, Env) a
> type Env  = M.Map IdInt IdInt

> unique :: LC IdInt -> U (LC IdInt)
> unique (Var v)   = Var <$> getVar v
> unique (Lam v e) = Lam <$> addVar v <*> unique e
> unique (App f a) = App <$> unique f <*> unique a

Add a variable to the mapping.

> addVar :: IdInt -> U IdInt
> addVar v = do
>    (i, env) <- get
>    put (succ i, M.insert v i env)
>    return i

Find an existing variable in the mapping.

> getVar :: IdInt -> U IdInt
> getVar v = do 
>   (_, m) <- get
>   return $ maybe v id (M.lookup v m)


> toUnique :: LC IdInt -> LC IdInt
> toUnique e = evalState (unique e) i where
>    i = (firstBoundId, M.empty)

"Unique variable" based alpha-equivalence: generate a fresh name for each
 binding variable.

> type Env2 = (M.Map IdInt IdInt, M.Map IdInt IdInt)
>

> addVar2 :: Env2 -> IdInt -> IdInt -> U Env2
> addVar2 (m1,m2) v1 v2 = do
>    (i,m) <- get
>    put (succ i,m)
>    return (M.insert v1 i m1, M.insert v2 i m2)
> getVar2 :: Env2 -> IdInt -> IdInt -> (IdInt,IdInt)
> getVar2 (m1,m2) v1 v2 = do
>     (fromMaybe v1 (M.lookup v1 m1), fromMaybe v2 (M.lookup v2 m2))

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq a b = evalState (uaeq (M.empty,M.empty) a b) (initState (App a b), M.empty)

> uaeq :: Env2 -> LC IdInt -> LC IdInt -> U Bool
> uaeq env (Var v1) (Var v2)       = do
>     let (v1', v2') = getVar2 env v1 v2
>     return $ v1' == v2'
> uaeq env (Lam v1 e1) (Lam v2 e2) = do
>     env' <- addVar2 env v1 v2
>     uaeq env' e1 e2
> uaeq env (App a1 a2) (App b1 b2) = liftM2 (&&) (uaeq env a1 b1) (uaeq env a2 b2)
> uaeq _env _u1 _u2 = return False

Note: we don't want to capture any free variables, so we need to start our
freshening function with the maxium variable found in the term.

> initState :: LC IdInt -> IdInt
> initState e = succ x where
>      vs = allVars e
>      x  = newId vs 

> newId :: [IdInt] -> IdInt
> newId [] = firstBoundId
> newId vs = succ (maximum vs)

> allVars :: LC IdInt -> [IdInt]
> allVars (Var v) = [v]
> allVars (Lam _ e) = allVars e
> allVars (App f a) = allVars f `union` allVars a
