-- | Parallel (explicit) substitutions, represented as a data structure.
module DeBruijn.Par.P (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Par.P",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data DB
  = DVar {-# UNPACK #-} !Int
  | DLam !DB
  | DApp !DB !DB
  deriving (Eq)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------

subst :: Sub -> DB -> DB
subst s = go
  where
    go (DVar i) = applySub s i
    go (DLam e) = DLam (substBind s e)
    go (DApp f a) = DApp (go f) (go a)

---------------------------------------------------------

nf :: DB -> DB
nf e@(DVar _) = e
nf (DLam e) = DLam (nf e)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

---------------------------------------------------------

nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n - 1) b
nfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    DLam b -> Stats.count >> nfi (n - 1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ DApp f' a

---------------------------------------------------------

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
    to vs (Lam x b) = DLam (to (x : vs) b)
    to vs (App f a) = DApp (to vs f) (to vs a)

fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)

---------------------------------------------------------
-- 3
data Sub = Inc {-# UNPACK #-} !Int | Cons !DB !Sub | !Sub :<> !Sub

applySub :: Sub -> Int -> DB
applySub (Inc y) x = DVar (y + x)
applySub (Cons t ts) x
  | x < 0 = DVar x
  | x == 0 = t
  | otherwise = applySub ts (x - 1)
applySub (s1 :<> s2) x = subst s2 (applySub s1 x)
{-# INLINEABLE applySub #-}

lift :: Sub -> Sub
lift s = Cons (DVar 0) (s :<> Inc 1) -- 1
{-# INLINEABLE lift #-}

single :: DB -> Sub
single t = Cons t (Inc 0)
{-# INLINEABLE single #-}

substBind :: Sub -> DB -> DB
substBind s = subst (lift s)
{-# INLINEABLE substBind #-}

instance Semigroup Sub where
  (<>) = (:<>)

instance Monoid Sub where
  mempty = Inc 0

instantiate :: DB -> DB -> DB
instantiate a b = subst (single b) a
{-# INLINEABLE instantiate #-}
