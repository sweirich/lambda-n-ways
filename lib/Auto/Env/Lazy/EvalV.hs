{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- Uses well-scoped debruijn syntax 
-- Uses Rebound library for closures
-- Only evaluation for closed terms
-- environment-based interpreter
module Auto.Env.Lazy.EvalV (toDB, impl) where

import Rebound
import Rebound.Env
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Text.PrettyPrint.HughesPJ
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Env.Lazy.EvalV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = error "NF unimpelemented",
      impl_nfi = error "NFI unimplemented",
      impl_eval = eval,
      impl_aeq = (==)
    }


data Term n where
  DVar :: (Fin n) -> Term n
  DLam :: (Term (S n)) -> Term n
  DApp :: (Term n) -> (Term n) -> Term n
  DBool :: Bool -> Term n
  DIf :: Term n -> Term n -> Term n -> Term n
-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (Term n)

instance NFData (Term a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

instance SubstVar Val where
  var = error "xx"
instance Subst Val Val where
  applyE r (VClos r' x) = VClos (r' .>> r) x
  applyE r (VBool x) = VBool x

----------------------------------------------------------

data Val m = forall n. VClos (Env Val n m) (Term (S n)) 
           | VBool Bool

---------------------------------------------------------

fromVal :: Val Z -> Term Z
fromVal (VBool b) = DBool b
fromVal (VClos env b) = error "not a ground type"

-- evaluate closed terms with an environment
eval :: Term Z -> Term Z
eval = fromVal . evalr zeroE

evalr :: Env Val m Z -> Term m -> Val Z
evalr r e@(DVar x) = applyEnv r x
evalr r (DLam e) = VClos r e
evalr r (DApp f a) =
  case evalr r f of
    VClos r' b -> evalr (evalr r a .: r') b
    f' -> error "stuck" 
evalr r (DBool b) = VBool b
evalr r (DIf a b c) = 
  case evalr r a of 
    VBool True -> evalr r b
    VBool False -> evalr r c
    a' -> error "stuck"
---------------------------------------------------------


toDB :: LC IdInt -> Term 'Z
toDB = to []
  where
    to :: [(IdInt, Fin n)] -> LC IdInt -> Term n
    to vs (Var v) = (DVar (fromJust (lookup v vs)))
    to vs (Lam v b) = (DLam b')
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b)  = (DBool b)
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
-- Convert back from deBruijn to the LC type.

fromDB :: Term n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Term n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b) (from n c)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

