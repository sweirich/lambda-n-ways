{-# LANGUAGE Strict #-}

-- This version uses parallel substitutions, represented as a data structure

-- It also caches substitutions at binders allowing them to
-- to be efficiently composed via smart constructors.

module DeBruijn.Par.B (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Debug.Trace
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
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Par.B",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "urk",
      impl_aeq = (==)
    }

data DB
  = DVar {-# UNPACK #-} Var
  | DApp DB DB
  | DLam {-# UNPACK #-} (Bind DB)
  deriving (Eq, Show)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------

var :: Var -> DB
var = DVar

subst :: Sub DB -> DB -> DB
subst s = go
  where
    go (DVar i) = applySub s i
    go (DLam b) = DLam (substBind s b)
    go (DApp f a) = DApp (go f) (go a)

---------------------------------------------------------

{-
-- try normalizing before substitution in a
-- beta reduction. But it doesn't work.
--
nf :: DB -> DB
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf f of
    (DLam b) -> nf (instantiate b (nf a))
    f' -> DApp (nf f') (nf a)

-}

nf :: DB -> DB
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf f of
    DLam b ->
      nf (instantiate b a)
    f' -> DApp (nf f') (nf a)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

---------------------------------------------------------

{-
nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam . bind <$> nfi (n -1) (unbind b)
nfi n (DApp f a) = do
  f' <- whnfi (n -1) (open f)
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$>  (nfi n f') <*> nfi n a

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a
-}
---------------------------------------------------------
-- Convert to deBruijn indicies.  Do this by keeping a list of the bound
-- variable so the depth can be found of all variables.  Do not touch
-- free variables.

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar (V i)) (DVar . V) (elemIndex v vs)
    to vs (Lam x b) = DLam (bind (to (x : vs) b))
    to vs (App f a) = DApp (to vs f) (to vs a)

fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar (V i))
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)

---------------------------------------------------------

{-
instance Show DB where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (unbind b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
-}
-----------------------------------------------------------

{-
potential optimizations

1. smart constructor in subst s2 (Bind s1 a)
2. smart constructor in lift
3. check for subst (Inc 0)
4. ! in Sub definition
5. ! in DB definition

NONE:   user	0m6.655s
1:      user	0m0.038s   (almost as fast at H, at user	0m0.030s)
1,2:    user	0m0.565s
2:      user    0m6.262s
1,3:    user	0m0.040s
1,4:    user	0m0.036s
1,4,5:  user	0m0.026s   (faster than H!)
1,2,4,5: (took too long!)
1,3,4,5: user	0m0.027s
1,3,4,5,6: user	0m0.010s
user	0m0.009s
-}

newtype Var = V Int deriving (Show, Eq, NFData)

data Bind a = Bind (Sub a) a

instance Show a => Show (Bind a) where
  show (Bind s a) = show s ++ show a

bind :: a -> Bind a
bind = Bind nil
{-# INLINE bind #-}

unbind :: Bind DB -> DB
unbind (Bind s a) = subst s a
{-# INLINE unbind #-}

instantiate :: Bind DB -> DB -> DB
instantiate (Bind s a) ~b = subst (s `comp` single b) a
{-# INLINE instantiate #-}

-- NOTE: use comp instead of :<>
substBind :: Sub DB -> Bind DB -> Bind DB
substBind ~s2 (Bind s1 e) = Bind (s1 `comp` lift s2) e
{-# INLINE substBind #-}

instance Eq (Bind DB) where
  (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

instance NFData a => NFData (Bind a) where
  rnf (Bind s a) = rnf s `seq` rnf a

-- 4 -- make all fields strict
-- NOTE: do *not* make first argument of Cons strict. See lams/regression1.lam
data Sub a
  = Inc {-# UNPACK #-} Int
  | Cons ~a !(Sub a) -- delay this so we don't evaluate the argument of a lambda expression
  | (Sub a) :<> (Sub a) -- f :<> g  is   subst g (subst f x)

instance Show (Sub a) where
  show (Inc 0) = "."
  show (Inc n) = "+" ++ show n
  show (Cons _ s) = "@" ++ show s
  show (s1 :<> s2) = show s1 ++ "<>" ++ show s2

----------------------------------------------------------------------

applySub :: Sub DB -> Var -> DB
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

lift :: Sub DB -> Sub DB
lift s = Cons (DVar (V 0)) (s :<> Inc 1)
{-# INLINE lift #-}

single :: a -> Sub a
single ~t = Cons t nil
{-# INLINE single #-}

-- smart constructor for composition
comp :: Sub DB -> Sub DB -> Sub DB
comp (Inc 0) s = s
comp s (Inc 0) = s
comp (Inc k1) (Inc k2) = Inc (k1 + k2)
comp (Inc n) (Cons _t s)
  | n > 0 = comp (Inc (n - 1)) s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

instance NFData a => NFData (Sub a) where
  rnf (Inc i) = rnf i
  rnf (Cons t ts) = rnf t `seq` rnf ts
  rnf (s1 :<> s2) = rnf s1 `seq` rnf s2