-- | Simplest use of the unbound-generics library
--   uses generic programming for Alpha/Subst instances
--   uses bind/subst during normalization
module Unbound.UnboundGenerics (impl) where

import qualified Control.DeepSeq as DS
import Control.Monad.Trans (lift)
import GHC.Generics (Generic)
import qualified Unbound.Generics.LocallyNameless as U
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Unbound.UnboundGenerics",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = U.aeq,
      impl_eval = whnf
    }

type Var = U.Name Exp

data Exp
  = Var !Var
  | Lam !(U.Bind Var Exp)
  | App !Exp !Exp
  | Bool {-# UNPACK #-} !Bool
  | If !Exp !Exp !Exp
  deriving (Show, Generic)

instance DS.NFData Exp where
  rnf (Var v) = DS.rnf v
  rnf (Lam b) = DS.rnf b
  rnf (App a b) = DS.rnf a `seq` DS.rnf b
  rnf (Bool b) = DS.rnf b
  rnf (If a b c) = DS.rnf a `seq` DS.rnf b `seq` DS.rnf c

-- | With generic programming, the default implementation of Alpha
-- provides alpha-equivalence, open, close, and free variable calculation.
instance U.Alpha Exp where
  {-# SPECIALIZE instance U.Alpha Exp #-}

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance U.Subst Exp Exp where
  {-# SPECIALIZE instance U.Subst Exp Exp #-}
  isvar (Var x) = Just (U.SubstName x)
  isvar _ = Nothing
  {-# INLINE U.isvar #-}

---------------------------------------------------------------

-- Normalization must be done in a freshness monad.
-- We use the one from unbound-generics
nf :: Exp -> Exp
nf = U.runFreshM . nfd

whnf :: Exp -> Exp
whnf = U.runFreshM . whnfd

nfd :: Exp -> U.FreshM Exp
nfd e@(Var _) = return e
nfd (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfd e'
    return $ Lam (U.bind x e1)
nfd (App f a) = do
  f' <- whnfd f
  case f' of
    Lam b -> do
      nfd (U.instantiate b [a])
    _ -> App <$> nfd f' <*> nfd a
nfd e@(Bool _) = return e
nfd (If a b c) = do
  a' <- whnfd a
  case a' of 
    Bool True -> nfd a
    Bool False -> nfd b
    a' -> If <$> (nfd a') <*> (nfd b) <*> (nfd c)

whnfd :: Exp -> U.FreshM Exp
whnfd e@(Var _) = return e
whnfd e@(Lam _) = return e
whnfd (App f a) = do
  f' <- whnfd f
  case f' of
    Lam b -> do
      whnfd (U.instantiate b [a])
    _ -> return $ App f' a
whnfd e@(Bool b) = return $ Bool b
whnfd (If a b c) = do
  a' <- whnfd a
  case a' of 
    Bool True -> whnfd b
    Bool False -> whnfd c
    a' -> return $ If a' b c
---------------------------------------------------------------

-- Convert from LC type to DB type (try to do this in linear time??)

toDB :: LC.LC IdInt -> Exp
toDB = to
  where
    to :: LC.LC IdInt -> Exp
    to (LC.Var v) = Var (i2n v)
    to (LC.Lam x b) = Lam (U.bind (i2n x) (to b))
    to (LC.App f a) = App (to f) (to a)
    to (LC.Bool b)  = Bool b
    to (LC.If a b c) = If (to a) (to b) (to c)

-- Convert back from deBruijn to the LC type.

n2i :: Var -> IdInt
n2i n = IdInt (fromInteger (U.name2Integer n))

i2n :: IdInt -> Var
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
    from (Bool b) = return $ LC.Bool b
    from (If a b c) = LC.If <$> (from a) <*> (from b) <*> (from c)
