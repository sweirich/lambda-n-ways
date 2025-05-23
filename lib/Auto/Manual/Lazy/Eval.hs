{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- Uses well-scoped debruijn syntax 
-- Doesn't use Rebound library (or bind type)
-- Only evaluation for closed terms
-- environment-based interpreter
-- environment represented by a function
module Auto.Manual.Lazy.Eval (toDB, impl) where

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
import Util.Nat
import Util.Syntax.Lazy.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Lazy.Eval",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = error "NF unimpelemented",
      impl_nfi = error "NFI unimplemented",
      impl_eval = eval,
      impl_aeq = (==)
    }

----------------------------------------------------------
type Env n = Idx n -> Thunk

data Thunk = 
   forall n. Thunk (Env n) (Term n)

data Val = forall n. VClos (Env n) (Term (S n)) | VBool Bool

nil :: Env Z 
nil x = case x of {}

(.:):: Thunk -> Env n  -> Env (S n)
v .: r = \x -> case x of { FZ -> v; FS y -> r y }

---------------------------------------------------------

fromVal :: Val -> Term Z
fromVal (VBool b) = DBool b
fromVal (VClos env b) = error "not a ground type"

evalThunk :: Thunk -> Val
evalThunk (Thunk r e) = evalr r e

-- evaluate closed terms with an environment
eval :: Term Z -> Term Z
eval = fromVal . evalr nil 

evalr :: Env m -> Term m -> Val
evalr r e@(DVar x) = evalThunk (r x)
evalr r (DLam e) = VClos r e
evalr r (DApp f a) =
  case evalr r f of
    VClos r' b -> evalr (Thunk r a .: r') b
    f' -> error "stuck" 
evalr r (DBool b) = VBool b
evalr r (DIf a b c) = 
  case evalr r a of 
    VBool True -> evalr r b
    VBool False -> evalr r c
    a' -> error "stuck"
---------------------------------------------------------
