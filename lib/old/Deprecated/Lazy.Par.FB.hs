-- This version uses Haskell functions to represent substitutions, but introduces
-- a 'Bind' abstract type to delay substitutions at binders.
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module DeBruijn.Lazy.Par.FB (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Text.PrettyPrint.HughesPJ
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import Util.Impl
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Lazy.Par.FB",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data DB
  = DVar Int
  | DLam (Bind DB)
  | DApp DB DB
  deriving (Eq)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------

instance SubstC DB where
  var = DVar

  subst s = go
    where
      go (DVar i) = applySub s i
      go (DLam b) = DLam (substBind s b)
      go (DApp f a) = DApp (go f) (go a)

----------------------------------------------------------

nfd :: DB -> DB
nfd e@(DVar _) = e
nfd (DLam e) = DLam (bind (nfd (unbind e)))
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate b a)
    f' -> DApp (nfd f') (nfd a)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

---------------------------------------------------------

nfi :: Int -> DB -> Stats.M DB
nfi 0 _ = Nothing
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam . bind <$> nfi (n -1) (unbind b)
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a

---------------------------------------------------------------

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
    to vs (Lam x b) = DLam (bind (to (x : vs) b))
    to vs (App f a) = DApp (to vs f) (to vs a)

fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)

-------------------------------------------------------

instance Show DB where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d

-----------------------------------------------------------
-----------------------------------------------------------

data Bind a = Bind !(Sub a) !a

bind :: SubstC a => a -> Bind a
bind = Bind nil
{-# INLINEABLE bind #-}

unbind :: SubstC a => Bind a -> a
unbind (Bind s a) = subst s a
{-# INLINEABLE unbind #-}

instantiate :: SubstC a => Bind a -> a -> a
instantiate (Bind s a) b = subst (s <> single b) a
{-# INLINEABLE instantiate #-}

substBind :: SubstC a => Sub a -> Bind a -> Bind a
substBind s2 (Bind s1 e) = Bind (s1 <> lift s2) e
{-# INLINEABLE substBind #-}

instance (SubstC a, Eq a) => Eq (Bind a) where
  (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

instance NFData a => NFData (Bind a) where
  rnf (Bind s a) = rnf s `seq` rnf a

---------------------------------------------------------------

newtype Sub a = Sub (Int -> a) deriving (NFData)

class SubstC a where
  var :: Int -> a
  subst :: Sub a -> a -> a

applySub :: SubstC a => Sub a -> Int -> a
{-# INLINEABLE applySub #-}
applySub (Sub f) = f

lift :: SubstC a => Sub a -> Sub a
{-# INLINEABLE lift #-}
lift s = consSub (var 0) (s <> incSub 1)

single :: SubstC a => a -> Sub a
{-# INLINEABLE single #-}
single t = consSub t nil

nil :: SubstC a => Sub a
{-# INLINEABLE nil #-}
nil = Sub var

incSub :: SubstC a => Int -> Sub a
{-# INLINEABLE incSub #-}
incSub y = Sub (\x -> var (y + x))

consSub :: SubstC a => a -> Sub a -> Sub a
{-# INLINEABLE consSub #-}
consSub t ts = Sub $ \x ->
  if x < 0
    then var x
    else
      if x == 0
        then t
        else applySub ts (x - 1)

instance SubstC a => Semigroup (Sub a) where
  s1 <> s2 = Sub $ \x -> subst s2 (applySub s1 x)

instance SubstC a => Monoid (Sub a) where
  mempty = nil

{-# SPECIALIZE applySub :: Sub DB -> Int -> DB #-}

{-# SPECIALIZE nil :: Sub DB #-}

{-# SPECIALIZE lift :: Sub DB -> Sub DB #-}

{-# SPECIALIZE single :: DB -> Sub DB #-}

{-# SPECIALIZE unbind :: Bind DB -> DB #-}

{-# SPECIALIZE instantiate :: Bind DB -> DB -> DB #-}

{-# SPECIALIZE substBind :: Sub DB -> Bind DB -> Bind DB #-}
