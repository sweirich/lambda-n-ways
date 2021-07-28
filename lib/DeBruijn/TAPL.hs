-- | This version is translated from the OCaml Code distributed with TAPL Ch. 7
-- "An untyped implementation of the Lambda Calculus"
-- Besides translation to Haskell, the implementation has been slightly simplified
-- (no info or string in the TmAbs, only one index in Var)
-- Block comments are quotes from TAPL
module DeBruijn.TAPL where

import Control.DeepSeq (NFData)
import Data.List (elemIndex)
import GHC.Generics (Generic)
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.TAPL",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "no nfi",
      impl_aeq = (==)
    }

{-
The representation of a variable is a number—its de Bruijn index. The
representation of an abstraction carries just a subterm for the abstraction’s body.
An application carries the two subterms being applied.
-}
data Term
  = Var {-# UNPACK #-} !Var
  | Lam !(Bind Term)
  | App !Term !Term
  deriving (Eq, Generic)

instance NFData Term

newtype Var = V Int deriving (Eq, Generic, NFData)

newtype Bind t = Bind t deriving (Eq, Generic, NFData)

{-
Given a term t and a function onvar, the result of tmmap onvar t is a term of the same shape as
t in which every variable has been replaced by the result of calling onvar on
that variable.

The arguments to 'onvar' are the current binding level (c) and the index of the
variable.
-}

tmMap :: (Int -> Var -> Term) -> Int -> Term -> Term
tmMap onvar = walk
  where
    walk c (Var x) = onvar c x
    walk c (Lam (Bind t2)) = Lam (Bind (walk (c + 1) t2))
    walk c (App t1 t2) = App (walk c t1) (walk c t2)

termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d = tmMap f where
  f c (V x) = if x >= c then Var (V (x + d)) else Var (V x)
{-# INLINE termShiftAbove #-}

termShift :: Int -> Term -> Term
termShift d t = termShiftAbove d 0 t
{-# INLINE termShift #-}

termSubst :: Var -> Term -> Term -> Term
termSubst (V j) s t = tmMap f where
  f c (V x) = if x == j + c then termShift c s else Var (V x)) 0 t
{-# INLINE termSubst #-}

termSubstTop :: Term -> Term -> Term
termSubstTop s t =
  termShift (-1) (termSubst (V 0) (termShift 1 s) t)
{-# INLINE termSubstTop #-}

{-
The treatment of substitution presented in this chapter, though sufficient
for our purposes in this book, is far from the final word on the subject. In
particular, the beta-reduction rule in our evaluator “eagerly” substitutes the
argument value for the bound variable in the function’s body. Interpreters
(and compilers) for functional languages that are tuned for speed instead of
simplicity use a different strategy: instead of actually performing the
substitution, we simply record an association between the bound variable name
and the argument value in an auxiliary data structure called the environment,
which is carried along with the term being evaluated. When we reach a variable,
we look up its value in the current environment. This strategy can be
modeled by regarding the environment as a kind of explicit substitution—i.e.,
by moving the mechanism of substitution from the meta-language into the
object language, making it a part of the syntax of the terms manipulated by
the evaluator, rather than an external operation on terms.
Explicit substitutions were first studied by Abadi, Cardelli, Curien,
and Lévy (1991a) and have since become an active research area.
-}

-------------------------------------------------------------------

nf :: Term -> Term
nf e@(Var _) = e
nf (Lam (Bind e)) = Lam (Bind (nf e))
nf (App f a) =
  case whnf f of
    Lam b -> nf (instantiate b a)
    f' -> App (nf f') (nf a)

whnf :: Term -> Term
whnf e@(Var _) = e
whnf e@(Lam _) = e
whnf (App f a) =
  case whnf f of
    Lam b -> whnf (instantiate b a)
    f' -> App f' a

nfb :: Bind Term -> Bind Term
nfb (Bind e) = Bind (nf e)
{-# INLINE nfb #-}

instantiate :: Bind Term -> Term -> Term
instantiate (Bind b) a = termSubstTop a b
{-# INLINE instantiate #-}

-------------------------------------------------------------------
toDB :: LC.LC IdInt -> Term
toDB = to []
  where
    to vs (LC.Var v@(IdInt i)) = maybe (Var (V i)) (Var . V) (elemIndex v vs)
    to vs (LC.Lam x b) = Lam (Bind (to (x : vs) b))
    to vs (LC.App f a) = App (to vs f) (to vs a)

fromDB :: Term -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (Var (V i))
      | i < 0 = LC.Var (IdInt i)
      | i >= n = LC.Var (IdInt i)
      | otherwise = LC.Var (IdInt (n - i -1))
    from n (Lam (Bind b)) = LC.Lam n (from (succ n) b)
    from n (App f a) = LC.App (from n f) (from n a)