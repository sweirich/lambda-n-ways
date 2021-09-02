{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Unbound.UnboundRep (impl) where

import qualified Control.DeepSeq as DS
import Control.Monad.Trans (lift)
import Data.Set (Set, lookupMax)
-- We cannot qualified the imports from unbound because of the use
-- of TemplateHaskell. Sigh.
import Unbound.LocallyNameless as U
  ( Alpha,
    Bind,
    FreshM,
    FreshMT,
    Name,
    R,
    Rep (..),
    Subst (isvar),
    SubstName (SubstName),
    aeq,
    bind,
    derive,
    fv,
    name2Integer,
    runFreshM,
    runFreshMT,
    s2n,
    substBind,
    unbind,
    type (:*:) ((:*:)),
  )
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import qualified Util.Lambda as LC
import qualified Util.Stats as Stats

type Var = U.Name Exp

data Exp
  = Var !Var
  | Lam !(U.Bind Var Exp)
  | App !Exp !Exp
  deriving (Show)

instance DS.NFData Exp where
  rnf (Var n) = DS.rnf n
  rnf (Lam bnd) = DS.rnf bnd
  rnf (App e1 e2) = DS.rnf e1 `seq` DS.rnf e2

-- Use RepLib to derive representation types

$(U.derive [''Exp])

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Unbound.UnboundRep",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfiTop,
      impl_aeq = U.aeq
    }

-- With representation types, the default implementation of Alpha
-- provides alpha-equivalence and free variable calculation.

instance U.Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance U.Subst Exp Exp where
  isvar (Var x) = Just (U.SubstName x)
  isvar _ = Nothing
  {-# INLINE U.isvar #-}

-- {-# SPECIALIZE U.aeq :: Exp -> Exp -> Bool #-}
-- {-# SPECIALIZE U.bind :: Var -> Exp -> U.Bind Var Exp #-}
-- {-# SPECIALIZE U.unbind :: U.Bind Var Exp -> U.FreshM (Var, Exp) #-}
-- {-# SPECIALIZE U.substBind :: U.Bind Var Exp -> Exp -> Exp #-}

---------------------------------------------------

nf :: Exp -> Exp
nf = U.runFreshM . nfd

--Computing the normal form proceeds as usual.

nfd :: Exp -> FreshM Exp
nfd e@(Var _) = return e
nfd (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfd e'
    return $ Lam (U.bind x e1)
nfd (App f a) =
  case whnf f of
    Lam b -> nfd (U.substBind b a)
    f' -> App <$> nfd f' <*> nfd a

--Compute the weak head normal form.

whnf :: Exp -> Exp
whnf e@(Var _) = e
whnf e@(Lam _) = e
whnf (App f a) =
  case whnf f of
    Lam b -> whnf (U.substBind b a)
    f' -> App f' a

nfiTop :: Int -> Exp -> Stats.M Exp
nfiTop x e = U.runFreshMT (nfi x e)

nfi :: Int -> Exp -> FreshMT Stats.M Exp
nfi 0 _ = lift Stats.done
nfi _ e@(Var _) = return e
nfi n (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfi (n -1) e'
    return $ Lam (U.bind x e1)
nfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    Lam b -> lift Stats.count >> nfi (n -1) (U.substBind b a)
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

--Compute the weak head normal form.

whnfi :: Int -> Exp -> FreshMT Stats.M Exp
whnfi 0 _ = lift Stats.done
whnfi _ e@(Var _) = return e
whnfi _ e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    Lam b -> do
      lift Stats.count
      whnfi (n -1) (U.substBind b a)
    _ -> return $ App f' a

--Convert from LC type to DB type (try to do this in linear time??)

toDB :: LC.LC IdInt -> Exp
toDB = to
  where
    to :: LC.LC IdInt -> Exp
    to (LC.Var v) = Var (i2n v)
    to (LC.Lam x b) = Lam (U.bind (i2n x) (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

n2i :: Var -> IdInt
n2i n = IdInt (fromInteger (U.name2Integer n))

i2n :: IdInt -> Var
i2n (IdInt x) = U.s2n (show x)

fromDB :: Exp -> LC.LC IdInt
fromDB = U.runFreshM . from
  where
    from :: Exp -> FreshM (LC.LC IdInt)
    from (Var n) = return $ LC.Var (n2i n)
    from (Lam b) = do
      (x, a) <- U.unbind b
      LC.Lam (n2i x) <$> from a
    from (App f a) = LC.App <$> from f <*> from a
