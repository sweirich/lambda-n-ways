{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}

-- | Well-scoped de Bruijn indices 
-- Doesn't use autoenv library, or a bind type
-- but otherwise uses ideas from it
-- with naive substitution, closed terms only
module Auto.Manual.Subst (toDB, impl) where

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
import Util.Syntax.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Subst",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = error "nf unimplemented",
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==),
      impl_eval = eval
    }

----------------------------------------------------------

type Sub m n = Idx m -> Term n                   

(.:) :: a -> (Idx m -> a) -> Idx (S m) -> a               -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

up :: Sub m n -> Sub (S m) (S n)                      -- shift
up s = \case
          FZ -> DVar  FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices
      
upZ :: Sub m Z -> Sub (S m) (S Z)                      -- shift
upZ s = \case
          FZ -> DVar FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices


apply :: Sub m n -> Term m -> Term n                    -- multi substitutions
apply r (DVar x)      = r x
apply r (DLam b)      = DLam (apply (up r) b)
apply r (DApp a1 a2)  = DApp (apply r a1) (apply r a2)
apply r (DIf a b c )  = DIf (apply r a) (apply r b) (apply r c)
apply r (DBool b)     = DBool b

subst :: Term n -> Term (S n) -> Term n                  -- single substitution
subst v = apply (v .: DVar)

----------------------------------------------------------

type NEnv n = Idx n -> NThunk 

data NThunk where 
  Suspend :: NEnv m -> Term m -> NThunk

force :: NThunk -> NVal
force (Suspend r a) = cbn r a

data NVal where
  NVLam :: NEnv m -> Term (S m) -> NVal

cbn :: NEnv m -> Term m -> NVal
cbn r (DVar x) = force (r x)
cbn r (DLam b) = NVLam r b
cbn r (DApp f a) = 
  case cbn r f of 
     NVLam r' b -> 
       cbn (Suspend r a .: r') b


----------------------------------------------------------

type Env n = Idx n -> Val

data Val where
  VLam :: Env m -> Term (S m) -> Val
  VBool :: Bool -> Val

evalE :: (Idx n -> Val) -> Term n -> Val
evalE r (DVar x) = r x
evalE r (DLam b) = VLam r b
evalE r (DApp f a) = case evalE r f of 
   VLam r' b -> evalE (evalE r a .: r') b
evalE r (DIf a b c) = case evalE r a of
   VBool True -> evalE r b
   VBool False -> evalE r c
evalE r (DBool b) = VBool b

toTerm :: Val -> Term Z
toTerm (VLam r e) = DLam (applyE (up (toTerm . r)) e)
toTerm (VBool b) = DBool b
-- 
applyE :: (Idx n -> Term m) -> Term n -> Term m
applyE r (DVar x) = r x
applyE r (DLam b) = 
  DLam (applyE (up r) b)
applyE r (DApp f a) = 
  DApp (applyE r f) (applyE r a)

-- Evaluate closed Termressions (call-by-name)
eval :: Term Z -> Term Z
eval e@(DLam b) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (subst a b)
    f' -> error "stuck"
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval a
    DBool False -> eval b
    _ -> error "stuck"