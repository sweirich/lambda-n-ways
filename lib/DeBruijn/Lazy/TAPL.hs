-- | This version is translated from the OCaml Code distributed with TAPL ch. 7
-- "An untyped implementation of the Lambda Calculus"
-- Besides translation to Haskell, it has been slightly simplified (no info, or string in the TmAbs)
module DeBruijn.Lazy.TAPL where

import Control.DeepSeq (NFData)
import Data.List (elemIndex)
import GHC.Generics (Generic)
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Lazy.TAPL",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

{-
The representation of a variable is a number—its de Bruijn index. The representation of an abstraction carries just a subterm for the abstraction’s body.
An application carries the two subterms being applied.

For purposes of debugging, it is helpful to carry an extra number on
each variable node, as a consistency check. The convention will be that this
second number will always contain the total length of the context in which
the variable occurs.
-}
data Term
  = TmVar Int
  | TmAbs Term
  | TmApp Term Term
  deriving (Eq, Generic)

instance NFData Term

{-
Given a term t and
a function onvar, the result of tmmap onvar t is a term of the same shape as
t in which every variable has been replaced by the result of calling onvar on
that variable.

The arguments to 'onvar' are the current binding level (c) and the index of the
variable.
-}

tmMap :: (Int -> Int -> Term) -> Int -> Term -> Term
tmMap onvar = walk
  where
    walk c (TmVar x) = onvar c x
    walk c (TmAbs t2) = TmAbs (walk (c + 1) t2)
    walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)

termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d =
  tmMap (\c x -> if x >= c then TmVar (x + d) else TmVar x)

termShift :: Int -> Term -> Term
termShift d t = termShiftAbove d 0 t

termSubst :: Int -> Term -> Term -> Term
termSubst j s t =
  tmMap (\c x -> if x == j + c then termShift c s else TmVar x) 0 t

termSubstTop :: Term -> Term -> Term
termSubstTop s t =
  termShift (-1) (termSubst 0 (termShift 1 s) t)

{-
The treatment of substitution presented in this chapter, though sufficient
for our purposes in this book, is far from the final word on the subject. In
particular, the beta-reduction rule in our evaluator “eagerly” substitutes the
argument value for the bound variable in the function’s body. Interpreters
(and compilers) for functional languages that are tuned for speed instead of
simplicity use a different strategy: instead of actually performing the substitution, we simply record an association between the bound variable name
and the argument value in an auxiliary data structure called the environment,
which is carried along with the term being evaluated. When we reach a variable, we look up its value in the current environment. This strategy can be
modeled by regarding the environment as a kind of explicit substitution—i.e.,
by moving the mechanism of substitution from the meta-language into the
object language, making it a part of the syntax of the terms manipulated by
the evaluator, rather than an external operation on terms. Explicit substitutions were first studied by Abadi, Cardelli, Curien, and Lévy (1991a) and have
since become an active research area.
-}

-------------------------------------------------------------------

nf :: Term -> Term
nf e@(TmVar _) = e
nf (TmAbs e) = TmAbs (nf e)
nf (TmApp f a) =
  case whnf f of
    TmAbs b -> nf (instantiate b a)
    f' -> TmApp (nf f') (nf a)

whnf :: Term -> Term
whnf e@(TmVar _) = e
whnf e@(TmAbs _) = e
whnf (TmApp f a) =
  case whnf f of
    TmAbs b -> whnf (instantiate b a)
    f' -> TmApp f' a

-------------------------------------------------------------------

nfi :: Int -> Term -> Stats.M Term
nfi 0 _e = Stats.done
nfi _n e@(TmVar _) = return e
nfi n (TmAbs b) = TmAbs <$> nfi (n -1) b
nfi n (TmApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    TmAbs b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> TmApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> Term -> Stats.M Term
whnfi 0 _e = Stats.done
whnfi _n e@(TmVar _) = return e
whnfi _n e@(TmAbs _) = return e
whnfi n (TmApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    TmAbs b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ TmApp f' a

instantiate :: Term -> Term -> Term
instantiate b a = termSubstTop a b
{-# INLINE instantiate #-}

toDB :: LC IdInt -> Term
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (TmVar i) TmVar (elemIndex v vs)
    to vs (Lam x b) = TmAbs (to (x : vs) b)
    to vs (App f a) = TmApp (to vs f) (to vs a)

fromDB :: Term -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (TmVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (TmAbs b) = Lam n (from (succ n) b)
    from n (TmApp f a) = App (from n f) (from n a)