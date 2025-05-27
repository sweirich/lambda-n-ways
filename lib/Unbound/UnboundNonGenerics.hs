-- | Simplest use of the unbound-generics library
--   uses generic programming for Alpha/Subst instances
--   uses bind/subst during normalization
module Unbound.UnboundNonGenerics (impl) where

import qualified Control.DeepSeq as DS
import Control.Monad.Trans (lift)
import GHC.Generics (Generic)
import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Bind as U
import qualified Unbound.Generics.LocallyNameless.Name as U
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Unbound.UnboundNonGenerics",
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


instance U.Alpha Exp where
  {-# SPECIALIZE instance U.Alpha Exp #-}
  open c np (Var n) = Var (U.open c np n)
  open c np (Lam bnd) = Lam (U.open c np bnd)
  open c np (App a1 a2) =
    App (U.open c np a1) (U.open c np a2)
  open c np (Bool b) = Bool b
  open c np (If a b1 b2) = If (U.open c np a) (U.open c np b1) 
    (U.open c np b2)
  {-# INLINE U.open #-}

  close c np (Var n) = Var (U.close c np n)
  close c np (Lam bnd) = Lam (U.close c np bnd)
  close c np (App a1 a2) =
    App (U.close c np a1) (U.close c np a2)
  close c np (Bool b) = Bool b
  close c np (If a b1 b2) = If (U.close c np a)
    (U.close c np b1) (U.close c np b2)
  {-# INLINE U.close #-}

  aeq' :: U.AlphaCtx -> Exp -> Exp -> Bool
  aeq' c (Var x) (Var y) = U.aeq' c x y
  aeq' c (Lam bnd1) (Lam bnd2) = U.aeq' c bnd1 bnd2
  aeq' c (App a1 a2) (App b1 b2) = U.aeq' c a1 b1 && U.aeq' c a2 b2
  aeq' c (Bool b1) (Bool b2) = b1 == b2
  aeq' c (If a b1 b2) (If a' b1' b2') = 
    U.aeq' c a a' && U.aeq' c b1 b1' && U.aeq' c b2 b2'
  aeq' _ _ _ = False
  {-# INLINE U.aeq' #-}

instance U.Subst Exp Exp where
  {-# SPECIALIZE instance U.Subst Exp Exp #-}

  -- subst :: Name a -> a -> b -> b
  subst :: U.Name Exp -> Exp -> Exp -> Exp
  subst x b a@(Var y) = if x == y then b else a
  subst x b (Lam bnd) = Lam (U.subst x b bnd)
  subst x b (App a1 a2) = App (U.subst x b a1) (U.subst x b a2)
  subst x b (Bool b1) = Bool b1
  subst x b (If a1 a2 a3) = If 
    (U.subst x b a1) (U.subst x b a2) (U.subst x b a3)
  substBvs :: U.AlphaCtx -> [Exp] -> Exp -> Exp
  substBvs ctx bs (Var x@(U.Bn j k)) 
     | U.ctxLevel ctx == j, fromInteger k < length bs = bs !! fromInteger k
  substBvs ctx bs (Var x) = Var x 
  substBvs ctx bs (Lam bnd) = 
    Lam (U.substBvs ctx bs bnd)
  substBvs ctx bs (App a1 a2) = 
    App (U.substBvs ctx bs a1) (U.substBvs ctx bs a2)
  substBvs ctx bs (Bool b) = Bool b
  substBvs ctx bs (If a b1 b2) = If (U.substBvs ctx bs a)
     (U.substBvs ctx bs b1) (U.substBvs ctx bs b2)
  {-# INLINE U.subst #-}


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
