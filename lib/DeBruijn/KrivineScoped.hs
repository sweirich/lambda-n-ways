module DeBruijn.KrivineScoped where

-- This implementation is based on
--    Crégut, P. (2007) Strongly reducing variants of the Krivine abstract machine. Higher-Order Symb.
--    Comput. 20(3), 209–230.
-- as described in
--
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/fullreducing-krivine-abstract-machine-kn-simulates-pure-normalorder-reduction-in-lockstep-a-proof-via-corresponding-calculus/F9D6AC47F4C2FC0903CD28AB451B37EC

-- This is an abstract machine that implements full normal-order reduction
-- This version uses well-scoped indices

import Data.Kind
import Data.Some
import qualified Unsafe.Coerce as Unsafe
import Util.Impl (LambdaImpl (..))
import Util.Nat
import qualified Util.Stats as Stats
import Util.Syntax.ScopedDeBruijn
import Util.Vec

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.KrivineScoped",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==)
    }

type Env n = Vec n Closure

data Closure
  = forall n. Closure (Term n) (Env n)
  | Level Int
  | forall n. Result (Term ('S n)) Int

data State = State
  { closure :: Closure,
    stack :: [Closure],
    level :: Int
  }

step :: State -> State
step (State {closure = Closure t0 e, stack = s, level = l}) = case t0 of
  DVar n -> case e of
    VCons c e1 -> case n of
      -- (3)
      FZ -> State {closure = c, stack = s, level = l}
      -- (2)
      FS m -> State {closure = Closure (DVar m) e1, stack = s, level = l}
  -- VNil -> error "unbound variable"
  DLam t -> case s of
    -- (5)
    (Closure u p' : s') ->
      State
        { closure = Closure t (VCons (Closure u p') e),
          stack = s',
          level = l
        }
    -- (6)
    _ ->
      State
        { closure = Closure t (VCons (Level (succ l)) e),
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
  case fromIntToIdx (l - n) of
    Some FZ ->
      State {closure = Result (DVar FZ) l, stack = s, level = l}
    Some (FS m) ->
      State {closure = Result (DVar (FS m)) l, stack = s, level = l}
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
      let t' = Unsafe.unsafeCoerce t
       in State
            { closure = Result (DLam t') l,
              stack = s',
              level = l'
            }
    -- (10)
    (Result m l'' : s') ->
      let t' = Unsafe.unsafeCoerce t
       in State
            { closure = Result (DApp m t') l'',
              stack = s',
              level = l'
            }
    [] -> error "final state"

initial :: Term 'Z -> State
initial t = State {closure = (Closure t VNil), stack = [], level = 0}

isLam :: Term n -> Bool
isLam (DLam _) = True
isLam _ = False

final :: State -> Bool
final (State {closure = Result t _l, stack = p, level = _l'}) =
  null p && isLam t
final _ = False

nf :: Term 'Z -> Term 'Z
nf te = go (initial te)
  where
    go (State {closure = Result t _, stack = []}) = Unsafe.unsafeCoerce t
    go s = go $! step s
