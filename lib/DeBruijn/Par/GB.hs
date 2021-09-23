-- This version uses parallel substitutions, represented as a data structure

-- It also caches substitutions at binders allowing them to
-- to be efficiently composed via smart constructors.

module DeBruijn.Par.GB (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import GHC.Generics (Generic (..))
import Support.Par.Subst
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
    { impl_name = "DeBruijn.Par.GB",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

data DB
  = DVar {-# UNPACK #-} !Var
  | DLam !(Bind DB)
  | DApp !DB !DB
  deriving (Eq, Generic)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

----------------------------------------------------------
instance VarC DB where
  var = DVar
  {-# INLINEABLE var #-}
  isvar (DVar i) = Just i
  isvar _ = Nothing

instance SubstC DB DB

---------------------------------------------------------

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

nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
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

{-# SPECIALIZE applySub :: Sub DB -> Var -> DB #-}

{-# SPECIALIZE comp :: Sub DB -> Sub DB -> Sub DB #-}

{-# SPECIALIZE unbind :: Bind DB -> DB #-}

{-# SPECIALIZE instantiate :: Bind DB -> DB -> DB #-}

{-# SPECIALIZE substBind :: Sub DB -> Bind DB -> Bind DB #-}

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
