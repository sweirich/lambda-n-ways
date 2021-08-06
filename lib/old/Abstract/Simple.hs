-- | Binding implementation based on IdInt
-- Similar to the Impl.Simple
module Abstract.Simple where

import Abstract.Class
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.List (union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S

-----------------------------------------------------

-- Use a newtype for IdInt so that we can
-- distinguish this implementation from others?
-- Unfortunately, role for LC is nominal so we cannot coerce
type Simple = IdInt

-----------------------------------------------------

freeVars :: LC Simple -> Set Simple
freeVars (Var v) = S.singleton v
freeVars (Lam b) = freeVars e S.\\ S.singleton v
  where
    (v, e) = runIdentity (unbind b)
freeVars (App f a) = freeVars f `S.union` freeVars a

instance BindingImpl IdInt where
  type Bnd Simple = (,) Simple (LC IdInt)
  type Subst Simple = Map Simple
  type BindM Simple = Identity

  runBindM = runIdentity

  singleton = M.singleton

  aeq :: LC Simple -> LC Simple -> BindM Simple Bool
  aeq x y = return $ aeqd x y
    where
      aeqd (Var v1) (Var v2) = v1 == v2
      aeqd (Lam (v1, e1)) (Lam (v2, e2))
        | v1 == v2 = aeqd e1 e2
        | v1 `elem` freeVars (Lam (v2, e2)) = False
        | otherwise = aeqd e1 (applyPermLC p e2)
        where
          p = extendPerm emptyPerm v1 v2
      aeqd (App a1 a2) (App b1 b2) =
        aeqd a1 b1 && aeqd a2 b2
      aeqd _ _ = False
  bind v a = return (v, a)
  unbind = return
  toLC = return
  fromLC = return
  subst m a = return (substDefault m a)
  instantiate (v, a) b = return $ substDefault (M.singleton v b) a

substDefault :: Map Simple (LC Simple) -> LC Simple -> LC Simple
substDefault ss b = sub (S.toList vs0) b
  where
    sub _ e@(Var v)
      | v `M.member` ss = ss M.! v
      | otherwise = e
    sub vs e@(Lam b)
      | v `M.member` ss = e
      | v `S.member` fvs = lam' v' (sub (v' : vs) e'')
      | otherwise = lam' v (sub (v : vs) e')
      where
        (v, e') = unbind' b
        v' = newId vs
        e'' = substDefault (M.singleton v (Var v')) e'
    sub vs (App f a) = App (sub vs f) (sub vs a)

    fvs = foldMap freeVars ss
    vs0 =
      fvs `S.union` allVars b
        `S.union` M.keysSet ss

-- make sure we don't rename v' to variable we are sub'ing for

type Perm v = (M.Map v v, M.Map v v)

applyPerm :: Ord v => Perm v -> v -> v
applyPerm (m1, m2) x
  | Just y <- M.lookup x m1 = y
  | Just y <- M.lookup x m2 = y
  | otherwise = x

applyPermLC :: Perm IdInt -> LC IdInt -> LC IdInt
applyPermLC m (Var x) = Var (applyPerm m x)
applyPermLC m (Lam (x, e)) = Lam (applyPerm m x, applyPermLC m e)
applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)

emptyPerm :: Perm v
emptyPerm = (M.empty, M.empty)

extendPerm :: Ord v => Perm v -> v -> v -> Perm v
extendPerm (m1, m2) x y = (M.insert x y m1, M.insert y x m2)

lookupVar :: Ord v => Map v v -> v -> v
lookupVar m x = M.findWithDefault x x m

toIdInt :: LC Simple -> LC IdInt
toIdInt e = evalState (conv e) (0, fvmap)
  where
    fvmap =
      Prelude.foldr
        (\(v, i) m -> M.insert v (IdInt i) m)
        M.empty
        (zip (S.toList (freeVars e)) [1 ..])

conv :: (BindingImpl v) => LC v -> FreshM v (LC IdInt)
conv (Var v) = Var <$> convVar v
conv (Lam b) = Lam <$> (bind' <$> convVar v <*> conv e)
  where
    (v, e) = unbind' b
conv (App f a) = App <$> conv f <*> conv a

-- | Gather all variables (bound and free) that are used in a term
allVars :: BindingImpl v => LC v -> Set v
allVars (Var v) = S.singleton v
allVars (Lam b) = allVars e where (_, e) = unbind' b
allVars (App f a) = allVars f `S.union` allVars a
