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
import qualified Util.Stats as Stats
import Util.Syntax.DeBruijn
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.TAPL",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

type Var = Int

{-
Given a term t and a function onvar, the result of tmmap onvar t is a term of the same shape as
t in which every variable has been replaced by the result of calling onvar on
that variable.

The arguments to 'onvar' are the current binding level (c) and the index of the
variable.
-}

tmap :: (Int -> Var -> DB) -> Int -> DB -> DB
tmap onvar = walk
  where
    walk c (DVar x) = onvar c x
    walk c (DLam t2) = DLam (walk (c + 1) t2)
    walk c (DApp t1 t2) = DApp (walk c t1) (walk c t2)
{-# INLINE tmap #-}

shift :: Int -> DB -> DB
shift d = tmap f 0
  where
    f c x = if x >= c then DVar (x + d) else DVar x
{-# INLINE shift #-}

subst :: Var -> DB -> DB -> DB
subst j t = tmap f 0
  where
    f c x = if x == j + c then shift c t else DVar x
{-# INLINE subst #-}

instantiate :: DB -> DB -> DB
instantiate b a = shift (-1) (subst 0 (shift 1 a) b)
{-# INLINE instantiate #-}

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

nf :: DB -> DB
nf e@(DVar _) = e
nf (DLam e) = DLam (nf e)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a
