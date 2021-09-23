-- | Uses new "substBind" addition to unbound-generics library
-- with this operation, the normalization function does not need
-- to unbind terms before instantiation, saving a step. However, this
-- operation is limited to single binding only
module Unbound.UGSubstBind (impl) where

import qualified Control.DeepSeq as DS
import GHC.Generics (Generic)
import qualified Unbound.Generics.LocallyNameless as U
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Unbound.UGSubstBind",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplementd for unbound",
      impl_aeq = U.aeq
    }

type Var = U.Name Exp

data Exp
  = Var !Var
  | Lam !(U.Bind (U.Name Exp) Exp)
  | App !Exp !Exp
  deriving (Show, Generic)

instance DS.NFData Exp

-- With representation types, the default implementation of Alpha
-- provides alpha-equivalence, open, close, and free variable calculation.

instance U.Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance U.Subst Exp Exp where
  isvar (Var x) = Just (U.SubstName x)
  isvar _ = Nothing
  {-# INLINE U.isvar #-}

{-# SPECIALIZE U.aeq :: Exp -> Exp -> Bool #-}

{-# SPECIALIZE U.bind :: Var -> Exp -> U.Bind Var Exp #-}

{-# SPECIALIZE U.unbind :: U.Bind Var Exp -> U.FreshM (Var, Exp) #-}

---------------------------------------------------------------

nf :: Exp -> Exp
nf = U.runFreshM . nfd

-- Computing the normal form proceeds as usual.

nfd :: Exp -> U.FreshM Exp
nfd e@(Var _) = return e
nfd (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfd e'
    return $ Lam (U.bind x e1)
nfd (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> nfd (U.substBind b a)
    _ -> App <$> nfd f' <*> nfd a

--Compute the weak head normal form.

whnf :: Exp -> U.FreshM Exp
whnf e@(Var _) = return e
whnf e@(Lam _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> whnf (U.substBind b a)
    _ -> return $ App f' a

---------------------------------------------------------------

-- Convert from LC type to DB type (try to do this in linear time??)

toDB :: LC.LC IdInt -> Exp
toDB = to
  where
    to :: LC.LC IdInt -> Exp
    to (LC.Var v) = Var (i2n v)
    to (LC.Lam x b) = Lam (U.bind (i2n x) (to b))
    to (LC.App f a) = App (to f) (to a)

--Convert back from deBruijn to the LC type.

n2i :: U.Name Exp -> IdInt
n2i n = IdInt (fromInteger (U.name2Integer n))

i2n :: IdInt -> U.Name Exp
i2n (IdInt x) = U.s2n (show x)

fromDB :: Exp -> LC.LC IdInt
fromDB = U.runFreshM . from
  where
    from :: Exp -> U.FreshM (LC.LC IdInt)
    from (Var n) = return $ LC.Var (n2i n)
    from (Lam b) = do
      (x, a) <- U.unbind b
      LC.Lam (n2i x) <$> from a
    from (App f a) = LC.App <$> from f <*> from a
