{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
module NBE.Contextual where

import Util.Nat
import Data.Kind
import Util.Impl
import Util.IdInt
import Util.Syntax.ScopedDeBruijn
import Util.Syntax.Lambda as LC
import Control.DeepSeq



impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.Contextual",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = error "undefined",
      impl_aeq = (==)
    }

-----------------------------------------------------
-- contextual embedding infrastructure

data ProxyTop (n :: Nat) :: Type where
    ProxyTop :: ProxyTop (S n)

instance NFData (ProxyTop n) where
    rnf ProxyTop = ()

class Ext m n where
    coerce :: ProxyTop m -> Idx n

instance {-# OVERLAPPING #-} Ext n n where
    coerce :: ProxyTop n -> Idx n
    coerce ProxyTop = FZ
instance {-# OVERLAPPABLE #-}
    (Ext n0 n1, n2 ~ S n1) => Ext n0 n2 where
    coerce :: ProxyTop n0 -> Idx n2
    coerce i = FS (coerce i)

data ExtE m n where
    Refl :: ExtE m m
    Step :: ExtE m n -> ExtE m (S n)


-- This type has an existential. But it is isomorphic 
-- to 'Idx' or 'Fin' because the Ext n m dictionary 
-- produces the Fin when applied to the Proxy
data Var n where
    Hua :: Ext n m => ProxyTop n -> Var m

var :: Ext n m => ProxyTop n -> Var m
var = Hua

instance NFData (Var n) where
    rnf :: Var n -> ()
    rnf (Hua ProxyTop) = ()

-- Compare for equality by converting to Fin
-- Have to do it this way because all of the 
-- information about the var is in 'Ext' constraint
instance Eq (Var n) where
    (==) :: Var n -> Var n -> Bool
    x == y = toIndex x == toIndex y

instance Show (Var n) where
    show :: Var n -> String
    show x = show (toIndex x)

toIndex :: Var n -> Idx n
toIndex (Hua i) = coerce i

fromIndex :: Idx n -> Var n
fromIndex FZ = v0
fromIndex (FS i) = vS (fromIndex i)

v0 :: forall m. Var (S m)
v0 = Hua (ProxyTop @m)

vS :: Var n -> Var (S n)
vS (Hua p) = Hua p

-- Some variables 

v1 :: Var (S (S n))
v1 = vS v0

v2 :: Var (S (S (S n)))
v2 = vS v1

-- >>> v1
-- 1


--------------------------------------------------------------
-- Substitutions
-- These are specialized to Exp, but could be generalized 
-- using a type class


type Sub n m = Idx n -> Exp m

-- shift a substitution into a new scope
lift :: Sub n m -> Sub (S n) (S m)
lift s = CVar v0 .: (s `comp` incE)

-- identity substitution
idE :: Sub n n
idE = CVar . fromIndex

-- increment
incE :: Sub n (S n)
incE x = CVar (vS (fromIndex x))

single :: Exp n -> Sub (S n) n
single t = t .: idE

comp :: Sub m n -> Sub n p -> Sub m p
comp s1 s2 x = s1 x |> s2

-- extended substitution (cons)
(.:) :: Exp m -> Sub n m -> Sub (S n) m
t .: r = \x -> case x of
                 FZ -> t
                 FS m -> r m

--------------------------------------------------------------
-- contextual interface to scoped debruijn?

--------------------------------------------------------------

data Exp :: Nat -> Type where
    CVar :: Var n -> Exp n
    CBool :: Bool -> Exp n
    CLam :: (ProxyTop (S n) -> Exp (S n)) -> Exp n
    CApp :: Exp n -> Exp n -> Exp n

instance NFData (Exp n) where
    rnf (CVar x) = rnf x
    rnf (CBool b) = rnf b
    rnf (CLam f) = rnf f
    rnf (CApp t1 t2) = rnf t1 `seq` rnf t2

-- apply substitution
(|>) :: Exp n -> Sub n m -> Exp m
CBool b |> r = CBool b
CVar x |> r = r (toIndex x)
CApp e1 e2 |> r = CApp (e1 |> r) (e2 |> r)
CLam e |> r = CLam (\_ -> e ProxyTop |> lift r)


unembed :: Exp n -> Term n
unembed (CVar x) = DVar (toIndex x)
unembed (CApp e1 e2) = DApp (unembed e1) (unembed e2)
unembed (CLam f) = DLam (unembed (f ProxyTop))
unembed (CBool b) = DBool b

embed :: Term n -> Exp n
embed (DVar x) = CVar (fromIndex x)
embed (DApp e1 e2) = CApp (embed e1) (embed e2)
embed (DLam e) = CLam (\_ -> embed e)
embed (DBool b) = CBool b

fromLC :: LC IdInt -> Exp Z
fromLC = embed . toDB

toLC :: Exp Z -> LC IdInt
toLC = fromDB . unembed

nf :: Exp n -> Exp n
nf e@(CVar x) = e
nf (CLam b) = CLam (nf . b)
nf (CApp f a) =
    case whnf f of
        CLam b -> nf (b ProxyTop |> single a)
        f' -> CApp (nf f') (nf a)

whnf :: Exp n -> Exp n
whnf e@(CVar _) = e
whnf e@(CLam _) = e
whnf (CApp f a) =
    case whnf f of
        CLam b -> whnf (b ProxyTop |> single a)
        f' -> CApp f' a

instance Eq (Exp n) where
    CVar i == CVar j = i == j
    CLam f == CLam g = f ProxyTop == g ProxyTop
    (CApp a1 a2) == CApp b1 b2 = a1 == b1 && a2 == b2
