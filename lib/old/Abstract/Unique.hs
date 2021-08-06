--The Unique module implements the Normal Form function by
--using Barendregt's variable convention, i.e., all bound
-- variables are unique.
module Abstract.Unique where

import Abstract.Class
import qualified Abstract.Simple as LC
import Control.Monad.State
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

-- The first step is to make all bound variables unique. We define a newtype
-- to track which terms have been renamed in this way.

newtype Unique = MkU {fromUnique :: IdInt}
  deriving (Eq, Show, NFData, Arbitrary, Ord, Read, Enum)

instance BindingImpl Unique where
  type Bnd Unique = (,) Unique (LC Unique)
  type Subst Unique = (,) Unique
  type BindM Unique = N

  runBindM = runN
  singleton = (,)

  aeq :: LC Unique -> LC Unique -> BindM Unique Bool
  aeq = uaeq (M.empty, M.empty)

  bind v a = return (v, a)
  unbind = return
  toLC a = undefined
  fromLC = toUnique
  subst m a = usubst m a

-- state monad to keep track of the next fresh variable
-- as well as the variables that we have seen so far.
type N = State Unique

-- generate a fresh variable
newVar :: N Unique
newVar = do
  i <- get
  put (succ i)
  return i

-- record the new name of each idInt when freshening
type Env = M.Map IdInt Unique

-- Add a variable to the mapping.
addVar :: Env -> IdInt -> N (Unique, Env)
addVar env v = do
  i <- get
  put (succ i)
  return (i, M.insert v i env)

-- Find an existing variable in the mapping.
getVar :: Env -> IdInt -> Unique
getVar m v = fromMaybe (coerce v) (M.lookup v m)

-- Traversal to systematically rename all bound variables so that they
-- are unique.

unique :: Env -> LC IdInt -> N (LC Unique)
unique env (Var v) = return $ Var (getVar env v)
unique env (Lam (v, e)) = do
  (i, env') <- addVar env v
  ulam i <$> unique env' e
unique env (App f a) = App <$> unique env f <*> unique env a

ulam :: Unique -> LC Unique -> LC Unique
ulam v e = Lam (v, e)

-- We can also clone terms and freshen their variables
-- in any context
clone :: Env -> LC Unique -> N (LC Unique)
clone = undefined

-- If we don't have any free variables, we can start with 0
runN :: N a -> a
runN m = evalState m (MkU firstBoundId)

toUnique :: LC IdInt -> N (LC Unique)
toUnique = unique M.empty

-- The freshen function converts a named-term by renaming all bound variables.
-- It works even if the term has free variables.
freshen :: LC IdInt -> LC Unique
freshen e = evalState (toUnique e) (MkU (initState e))

--Note: we don't want to capture any free variables, so we need to start our
--freshening function with the maxium variable found in the term.
initState :: LC IdInt -> IdInt
initState e = succ x
  where
    vs = LC.allVars e
    x = if S.null vs then firstBoundId else max firstBoundId (maximum vs)

{-
Substitution proceeds by cloning the term that is inserted
at every place it is put.

(TODO: No need to clone $\lambda$-free terms.)
-}

usubst :: (Unique, LC Unique) -> LC Unique -> N (LC Unique)
usubst (x, s) = sub
  where
    sub e@(Var v)
      | v == x = clone M.empty s
      | otherwise = return e
    sub (Lam (v, e)) = ulam v <$> sub e
    sub (App f a) = App <$> sub f <*> sub a

{-
Do the actual translation of the term to unique variables.
We keep mapping of old variable names to new variable name.
Free variables are just left alone since they are already
uniquely named.
-}

-- "Unique variable" based alpha-equivalence: generate a fresh name for each
--  binding variable.

type Env2 = (M.Map Unique Unique, M.Map Unique Unique)

addVar2 :: Env2 -> Unique -> Unique -> N Env2
addVar2 (m1, m2) v1 v2 = do
  i <- get
  put (succ i)
  return (M.insert v1 i m1, M.insert v2 i m2)

getVar2 :: Env2 -> Unique -> Unique -> (Unique, Unique)
getVar2 (m1, m2) v1 v2 = do
  (fromMaybe v1 (M.lookup v1 m1), fromMaybe v2 (M.lookup v2 m2))

uaeq :: Env2 -> LC Unique -> LC Unique -> N Bool
uaeq env (Var v1) (Var v2) = do
  let (v1', v2') = getVar2 env v1 v2
  return $ v1' == v2'
uaeq env (Lam (v1, e1)) (Lam (v2, e2)) = do
  env' <- addVar2 env v1 v2
  uaeq env' e1 e2
uaeq env (App a1 a2) (App b1 b2) = liftM2 (&&) (uaeq env a1 b1) (uaeq env a2 b2)
uaeq _env _u1 _u2 = return False
