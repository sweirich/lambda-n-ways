{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}

-- | Well-scoped de Bruijn indices 
-- Doesn't use Rebound library (or bind type)
-- no bind type. evaluation based on substitution only

module Auto.Manual.Strict.Subst (toDB, impl) where

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
import Util.Nat
-- uses standard, scoped syntax
import Util.Syntax.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Strict.Subst",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==),
      impl_eval = eval
    }

----------------------------------------------------------

type Sub m n = Idx m -> Term n                   

(.:) :: a -> (Idx m -> a) -> Idx (S m) -> a            -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

up :: Sub m n -> Sub (S m) (S n)                       -- shift
up s = \case
          FZ -> DVar  FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices
      
apply :: Sub m n -> Term m -> Term n                    -- multi substitutions
apply r (DVar x)      = r x
apply r (DLam b)      = DLam (apply (up r) b)
apply r (DApp a1 a2)  = DApp (apply r a1) (apply r a2)
apply r (DIf a b c )  = DIf (apply r a) (apply r b) (apply r c)
apply r (DBool b)     = DBool b

instantiate :: Term (S n) -> Term n -> Term n                  -- single substitution
instantiate b v = apply (v .: DVar) b

----------------------------------------------------------

-- Evaluate closed terms with substitution
eval :: Term Z -> Term Z
eval e@(DLam b) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (instantiate b a)
    f' -> error "stuck"
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval a
    DBool False -> eval b
    _ -> error "stuck"

----------------------------------------------------------

nf :: Term n -> Term n
nf e@(DVar _) = e
nf (DLam b) = DLam (nf b)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a) (nf b) (nf c)

whnf :: Term n -> Term n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c