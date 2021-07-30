--This is a general purpose library for defining substitution for debruijn indices

module Support.Par.Subst where

import Control.DeepSeq

data Bind a = Bind !(Sub a) !a deriving (Show)

bind :: SubstC a => a -> Bind a
bind = Bind nil
{-# INLINABLE bind #-}

unbind :: SubstC a => Bind a -> a
unbind (Bind s a) = subst s a
{-# INLINABLE unbind #-}

instantiate :: SubstC a => Bind a -> a -> a
instantiate (Bind s a) b = subst (s <> single b) a
{-# INLINABLE instantiate #-}

substBind :: SubstC a => Sub a -> Bind a -> Bind a
  -- NOTE: use comp instead of :<>
substBind s2 (Bind s1 e) = Bind (s1 <> lift s2) e
{-# INLINABLE substBind #-}

instance (SubstC a, Eq a) => Eq (Bind a) where
   (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

instance NFData a => NFData (Bind a) where
  rnf (Bind s a) = rnf s `seq` rnf a


-- 4 -- make all fields strict
-- NOTE: do *not* make first argument of Cons strict. See lams/regression1.lam
data Sub a = Inc !Int
      | Cons a !(Sub a)
      | !(Sub a) :<> !(Sub a)
   deriving Show


class SubstC a where
   var   :: Int -> a
   subst :: Sub a -> a -> a

applySub :: SubstC a => Sub a -> Int -> a
applySub (Inc y)     x = var (y + x)
applySub (Cons t ts) x
           | x > 0     = applySub ts (x - 1) 
           | x == 0    = t
           | otherwise = var x 
applySub (s1 :<> s2) x = subst s2 (applySub s1 x)
{-# INLINABLE applySub #-}


nil :: SubstC a => Sub a
nil = Inc 0
{-# INLINABLE nil #-}

-- NOTE: adding a smart constructor in lift really slows things down!

lift :: SubstC a => Sub a -> Sub a
{-# INLINABLE lift #-}
lift s   = Cons (var 0) (s :<> Inc 1)

single :: SubstC a => a -> Sub a
{-# INLINABLE single #-}
single t = Cons t nil



-- smart constructor for composition
comp :: SubstC a => Sub a -> Sub a -> Sub a
comp (Inc k1) (Inc k2)  = Inc (k1 + k2)
comp (Inc 0) s       = s
comp (Inc n) (Cons _t s)
          | n > 0 = comp (Inc (n - 1)) s
comp s (Inc 0)   = s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINABLE comp #-}


instance SubstC a => Semigroup (Sub a) where
  (<>) = comp
instance SubstC a => Monoid (Sub a) where
  mempty  = nil
  mappend = (<>)

instance NFData a => NFData (Sub a) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2


