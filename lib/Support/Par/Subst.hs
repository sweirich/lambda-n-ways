--This is a general purpose library for defining substitution for debruijn indices
{-# LANGUAGE DefaultSignatures #-}

module Support.Par.Subst where

import Control.DeepSeq
import GHC.Generics

newtype Var = V Int deriving (Show, Eq, NFData, Generic)

data Bind a = Bind !(Sub a) !a deriving (Show)

bind :: a -> Bind a
bind = Bind nil
{-# INLINE bind #-}

unbind :: SubstC a a => Bind a -> a
unbind (Bind s a) = subst s a
{-# INLINE unbind #-}

instantiate :: SubstC a a => Bind a -> a -> a
instantiate (Bind s a) b = subst (s `comp` single b) a
{-# INLINE instantiate #-}

substBind :: (SubstC a a, VarC a) => Sub a -> Bind a -> Bind a
-- NOTE: use comp instead of :<>
substBind s2 (Bind s1 e) = Bind (s1 `comp` lift s2) e
{-# INLINE substBind #-}

instance (SubstC a a, Eq a) => Eq (Bind a) where
  (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

instance NFData a => NFData (Bind a) where
  rnf (Bind s a) = rnf s `seq` rnf a

-- 4 -- make all fields strict
-- NOTE: do *not* make first argument of Cons strict. See lams/regression1.lam
data Sub a
  = Inc !Int
  | Cons a !(Sub a)
  | !(Sub a) :<> !(Sub a)
  deriving (Show)

----------------------------------------------------------------------

class VarC a where
  var :: Var -> a
  isvar :: a -> Maybe Var
  isvar _ = Nothing
  {-# INLINE isvar #-}

class SubstC b a where
  subst :: Sub b -> a -> a
  default subst :: (Generic a, GSubst b (Rep a), VarC a, a ~ b) => Sub b -> a -> a
  subst s x =
    case (isvar x) of
      Just v -> applySub s v
      Nothing -> to $ gsubst s (from x)
  {-# INLINE subst #-}

-- Use this for a default definition when b /= a
-- instance (Generic a, GSubst b (Rep a)) => SubstC b a where
--  subst s x = to $ gsubst s (from x)

applySub :: (SubstC a a, VarC a) => Sub a -> Var -> a
applySub (Inc y) (V x) = var (V (y + x))
applySub (Cons t ts) (V x)
  | x > 0 = applySub ts (V (x - 1))
  | x == 0 = t
  | otherwise = var (V x)
applySub (s1 :<> s2) x = subst s2 (applySub s1 x)
{-# INLINEABLE applySub #-}

nil :: Sub a
nil = Inc 0
{-# INLINEABLE nil #-}

-- NOTE: adding a smart constructor in lift really slows things down!
-- so make sure that you keep the :<>

lift :: (VarC a) => Sub a -> Sub a
lift s = Cons (var (V 0)) (s :<> Inc 1)
{-# INLINE lift #-}

single :: a -> Sub a
single t = Cons t nil
{-# INLINE single #-}

-- smart constructor for composition
comp :: SubstC a a => Sub a -> Sub a -> Sub a
comp (Inc k1) (Inc k2) = Inc (k1 + k2)
comp (Inc 0) s = s
comp (Inc n) (Cons _t s)
  | n > 0 = comp (Inc (n - 1)) s
comp s (Inc 0) = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

instance NFData a => NFData (Sub a) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

-----------------------------------------------

newtype Ignore a = Ignore a

class GSubst b f where
  gsubst :: Sub b -> f a -> f a

-- Constant types
instance (SubstC b c) => GSubst b (K1 i c) where
  gsubst s (K1 c) = K1 (subst s c)
  {-# INLINE gsubst #-}

instance GSubst b U1 where
  gsubst _s U1 = U1
  {-# INLINE gsubst #-}

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1
  {-# INLINE gsubst #-}

instance GSubst b V1 where
  gsubst _s = id
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g
  {-# INLINE gsubst #-}

instance SubstC b (Ignore a) where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b Int where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b Bool where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b () where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b Char where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b String where
  subst _ = id
  {-# INLINE subst #-}

instance SubstC b Var where
  subst _ = id
  {-# INLINE subst #-}

instance (VarC b, SubstC b b) => SubstC b (Bind b) where
  subst = substBind
  {-# INLINE subst #-}

instance (Generic a, GSubst b (Rep [a])) => SubstC b [a] where
  subst s x = to $ gsubst s (from x)
  {-# INLINE subst #-}

instance (Generic a, GSubst b (Rep (Maybe a))) => SubstC b (Maybe a) where
  subst s x = to $ gsubst s (from x)
  {-# INLINE subst #-}

instance (Generic (Either a1 a2), GSubst b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  subst s x = to $ gsubst s (from x)
  {-# INLINE subst #-}

instance (Generic (a, b), GSubst c (Rep (a, b))) => SubstC c (a, b) where
  subst s x = to $ gsubst s (from x)
  {-# INLINE subst #-}

instance (Generic (a, b, d), GSubst c (Rep (a, b, d))) => SubstC c (a, b, d) where
  subst s x = to $ gsubst s (from x)
  {-# INLINE subst #-}