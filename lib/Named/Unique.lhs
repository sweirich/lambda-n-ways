The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Named.Unique(nf,Named.Unique.aeq, 
>                       toUnique, fromUnique, impl, Unique) where
> import Util.Syntax.Lambda as LC
> import qualified Data.Map as M
> import qualified Util.IdInt.Set as S
> import Control.Monad.State
> import Control.Monad
> import Util.IdInt
> import Data.Maybe (fromMaybe)
> import Data.Coerce
> import Control.DeepSeq
> 
> import Test.QuickCheck
> import qualified Util.Stats as Stats

> import Util.Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Named.Unique"
>           , impl_fromLC = toUnique
>           , impl_toLC   = fromUnique
>           , impl_nf     = nfd
>           , impl_nfi    = nfi
>           , impl_aeq    = aeq'
>        }


The first step is to make all bound variables unique. We define a newtype
to track which terms have been renamed in this way. 

> newtype Unique = MkU { fromUnique :: LC IdInt } deriving (Eq, Show, NFData)

We can also define some fake constructors to help us work with this new type.

> ulam :: IdInt -> Unique -> Unique
> ulam = coerce (Lam @IdInt)

> uapp :: Unique -> Unique -> Unique
> uapp = coerce (App @IdInt)

The freshen function converts a named-term by renaming all bound variables.

> freshen :: LC IdInt -> (Unique, IdInt)
> freshen e = runState (unique M.empty e) (initState e)

> toUnique :: LC IdInt -> Unique
> toUnique e = fst (freshen e)

Note: we don't want to capture any free variables, so we need to start our
freshening function with the maxium variable found in the term.

> initState :: LC IdInt -> IdInt
> initState e = succ x where
>      vs = LC.allVars e
>      x  = newId vs 

Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.

> nf :: LC IdInt -> LC IdInt
> nf e = fromUnique $ evalState (nf' e') i
>   where (e', i) = freshen e


Our state monad. 

> type N a = State IdInt a

> nfd :: Unique -> Unique
> nfd e = evalState (nf' e) (initState (fromUnique e))

> nf' :: Unique -> N Unique
> nf' e@(MkU (Var _)) = return e
> nf' (MkU (Lam x e)) = ulam x <$> nf' (MkU e)
> nf' (MkU (App f a)) = do
>     f' <- whnf (MkU f)
>     case f' of
>         MkU (Lam x b) -> subst x (MkU a) (MkU b) >>= nf'
>         _ -> uapp <$> nf' f' <*> nf' (MkU a)

Compute the weak head normal form.

> whnf :: Unique -> N Unique
> whnf e@(MkU (Var _)) = return e
> whnf e@(MkU (Lam _ _)) = return e
> whnf (MkU (App f a)) = do
>     f' <- whnf (MkU f)
>     case f' of
>         MkU (Lam x b) -> subst x (MkU a) (MkU b) >>= whnf
>         _ -> return $ uapp f' (MkU a)

Fueled version:

> type NM a = Stats.FM a

> nfi :: Int -> Unique -> Stats.M Unique
> nfi x e = result where
>     result = Stats.runF (nfi' x e) (initState (fromUnique e))

> nfi' :: Int -> Unique -> NM Unique
> nfi' 0 _ = Stats.doneFM
> nfi' _i e@(MkU (Var _)) = return e
> nfi' i (MkU (Lam x e)) = ulam x <$> nfi' (i-1)  (MkU e)
> nfi' i (MkU (App f a)) = do
>     f' <- whnfi (i-1) (MkU f)
>     case f' of
>         MkU (Lam x b) -> do
>               Stats.countFM
>               t <- subst x (MkU a) (MkU b)
>               nfi' (i-1) t
>         _ -> uapp <$> nfi' (i-1) f' <*> nfi' (i-1) (MkU a)

Compute the weak head normal form.

> whnfi :: Int -> Unique -> NM Unique
> whnfi 0 _ = Stats.doneFM
> whnfi _ e@(MkU (Var _)) = return e
> whnfi _ e@(MkU (Lam _ _)) = return e
> whnfi i (MkU (App f a)) = do
>     f' <- whnfi (i-1) (MkU f)
>     case f' of
>         MkU (Lam x b) -> Stats.countFM >> subst x (MkU a) (MkU b) >>= whnfi (i-1)
>         _ -> return $ uapp f' (MkU a)


<< TODO >>



Substitution proceeds by cloning the term that is inserted
at every place it is put.

(TODO: No need to clone $\lambda$-free terms.)

> subst :: forall m. (MonadState IdInt m) => IdInt -> Unique -> Unique -> m Unique
> subst x s = sub
>  where 
>        sub e@(MkU (Var v)) | v == x    = clone M.empty s
>                            | otherwise = return e
>        sub (MkU (Lam v e)) = ulam v <$> sub (MkU e)
>        sub (MkU (App f a)) = uapp <$> sub (MkU f) <*> sub (MkU a)
>
> {-       clone :: M.Map IdInt IdInt -> Unique -> m Unique
>        clone m e@(MkU (Var v)) = return $ maybe e uvar (M.lookup v m)
>        clone m (MkU (Lam v e)) = do v' <- newVar; liftM (ulam v') (clone (M.insert v v' m) (MkU e))
>        clone m (MkU (App f a)) = liftM2 uapp (clone m (MkU f)) (clone m (MkU a)) -}
>

> clone :: forall m. (MonadState IdInt m) => Env -> Unique -> m Unique
> clone = coerce $ unique @m


Do the actual translation of the term to unique variables.
We keep mapping of old variable names to new variable name.
Free variables are just left alone since they are already
uniquely named.

> type U a  = State IdInt a
> type Env  = M.Map IdInt IdInt

> unique :: MonadState IdInt m => Env -> LC IdInt -> m Unique
> unique env (Var v)   = return $ MkU $ Var (getVar env v)
> unique env (Lam v e) = do
>    (i, env') <- addVar env v
>    ulam i <$> unique env' e
> unique env (App f a) = uapp <$> unique env f <*> unique env a

Add a variable to the mapping.

> addVar :: MonadState IdInt m => Env -> IdInt -> m (IdInt,Env)
> addVar env v = do
>    i <- get
>    put (succ i)
>    return (i, M.insert v i env)

Find an existing variable in the mapping.

> getVar :: Env -> IdInt -> IdInt
> getVar m v = fromMaybe v (M.lookup v m)


"Unique variable" based alpha-equivalence: generate a fresh name for each
 binding variable.

> type Env2 = (M.Map IdInt IdInt, M.Map IdInt IdInt)
>

> addVar2 :: Env2 -> IdInt -> IdInt -> U Env2
> addVar2 (m1,m2) v1 v2 = do
>    i <- get
>    put (succ i)
>    return (M.insert v1 i m1, M.insert v2 i m2)
> getVar2 :: Env2 -> IdInt -> IdInt -> (IdInt,IdInt)
> getVar2 (m1,m2) v1 v2 = do
>     (fromMaybe v1 (M.lookup v1 m1), fromMaybe v2 (M.lookup v2 m2))

> aeq' :: Unique -> Unique -> Bool
> aeq' = coerce Named.Unique.aeq

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq a b = evalState (uaeq (M.empty,M.empty) a b) (initState (App a b))

> uaeq :: Env2 -> LC IdInt -> LC IdInt -> U Bool
> uaeq env (Var v1) (Var v2)       = do
>     let (v1', v2') = getVar2 env v1 v2
>     return $ v1' == v2'
> uaeq env (Lam v1 e1) (Lam v2 e2) = do
>     env' <- addVar2 env v1 v2
>     uaeq env' e1 e2
> uaeq env (App a1 a2) (App b1 b2) = liftM2 (&&) (uaeq env a1 b1) (uaeq env a2 b2)
> uaeq _env _u1 _u2 = return False

