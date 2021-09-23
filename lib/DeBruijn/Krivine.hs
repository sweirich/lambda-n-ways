module DeBruijn.Krivine where

-- This is an abstract machine (KN machine) that implements full normal-order reduction

-- This implementation is based on
--    Crégut, P. (2007) Strongly reducing variants of the Krivine abstract machine. Higher-Order Symb.
--    Comput. 20(3), 209–230.
-- as described in
--
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/fullreducing-krivine-abstract-machine-kn-simulates-pure-normalorder-reduction-in-lockstep-a-proof-via-corresponding-calculus/F9D6AC47F4C2FC0903CD28AB451B37EC

-- It is a variant of the Krivine machine that also handles open terms

import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.DeBruijn

-- typed version 14.9 ms
-- untyped version 13.7 ms
-- strict fields 13.3 ms

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Krivine",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==)
    }

type Env = [Closure]

data Closure
  = Closure !DB !Env
  | Level {-# UNPACK #-} !Int
  | Result !DB !Int

data State = State
  { closure :: !Closure,
    stack :: ![Closure],
    level :: {-# UNPACK #-} !Int
  }

step :: State -> State
step (State {closure = Closure t0 e, stack = s, level = l}) = case t0 of
  DVar n -> case e of
    c : e1 -> case n of
      -- (3)
      0 -> State {closure = c, stack = s, level = l}
      -- (2)
      _ -> State {closure = Closure (DVar (n - 1)) e1, stack = s, level = l}
    [] -> error "unbound variable"
  DLam t -> case s of
    -- (5)
    (Closure u p' : s') ->
      State
        { closure = Closure t ((Closure u p') : e),
          stack = s',
          level = l
        }
    -- (6)
    _ ->
      State
        { closure = Closure t ((Level (succ l)) : e),
          stack = Level (succ l) : s,
          level = succ l
        }
  -- (4)
  DApp t u ->
    State
      { closure = Closure t e,
        stack = Closure u e : s,
        level = l
      }
-- (7)
step (State {closure = Level n, stack = s, level = l}) =
  State {closure = Result (DVar (l - n)) l, stack = s, level = l}
step (State {closure = Result t l, stack = s, level = l'}) =
  case s of
    -- (8)
    (Closure u e : s') ->
      State
        { closure = Closure u e,
          stack = (Result t l) : s',
          level = l
        }
    -- (9)
    (Level _ : s') ->
      State
        { closure = Result (DLam t) l,
          stack = s',
          level = l'
        }
    -- (10)
    (Result m l'' : s') ->
      State
        { closure = Result (DApp m t) l'',
          stack = s',
          level = l'
        }
    [] -> error "final state"

initial :: DB -> State
initial t = State {closure = (Closure t []), stack = [], level = 0}

isLam :: DB -> Bool
isLam (DLam _) = True
isLam _ = False

final :: State -> Bool
final (State {closure = Result t _l, stack = p, level = _l'}) =
  null p && isLam t
final _ = False

nf :: DB -> DB
nf te = go (initial te)
  where
    go (State {closure = Result t _, stack = []}) = t
    go s = go $! step s
