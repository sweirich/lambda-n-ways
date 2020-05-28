\begin{code}

{-
 - Alternative De Bruijn index based lambda calculus interpreter
 - 
 - Author: Bertram Felgenhauer <int-e@gmx.de>
 -}

module DeBruijnC (nf,aeq,nfd,fromLC,toLC) where

import Lambda
import IdInt
import Data.List
import Control.DeepSeq

data DB v = DFree v              -- free variable
          | DBound Int           -- bound variable, uses de Bruijn index
          | DLam (DB v)          -- lambda abstraction (unbound)
          | DApp (DB v) (DB v)   -- application
          | DCont (DB v) [DB v]  -- lambda abstraction (bound to a context)
   deriving (Eq)

instance NFData a => NFData (DB a) where
   rnf (DFree i) = rnf i
   rnf (DBound i) = rnf i
   rnf (DLam d) = rnf d
   rnf (DApp a b) = rnf a `seq` rnf b
   rnf (DCont x y) = rnf x `seq` rnf y


nfd :: DB IdInt -> DB IdInt
nfd = dbnf []

-- Reduce DB expression to normal form.
dbnf :: [DB v] -> (DB v) -> (DB v)
dbnf   _ (DFree v)  = DFree v
dbnf ctx (DBound i) = ctx !! i
dbnf ctx (DLam t)   = DCont t ctx
dbnf ctx (DApp t s) = let t' = dbnf ctx t
                          s' = dbnf ctx s in
                      case t' of
                          DCont t'' ctx' -> dbnf (s':ctx') t''
                          _              -> DApp t' s'
dbnf   _ (DCont _ _) = error "dbnf: cound DCont"

aeq :: LC IdInt -> LC IdInt -> Bool
aeq x y = aeqd (fromLC [] x) (fromLC [] y)

aeqd :: DB IdInt -> DB IdInt -> Bool
aeqd (DFree v1) (DFree v2) = v1 == v2
aeqd (DBound i1) (DBound i2) = i1 == i2
aeqd (DApp a1 a2) (DApp b1 b2) = a1 == b1 && a2 == b2
aeqd (DCont _ _) (DCont _ _) = error "found DCont in aeqd"
aeqd _ _ = False


-- wrapper
nf :: LC IdInt -> LC IdInt
nf = toLC 0 . dbnf [] . fromLC []

-- Convert from DB form. The tricky part is to decode the Cont stuff to
-- lambda expressions again. The code call dbnf with a suitable context
-- in that case.
toLC :: Int -> DB IdInt -> LC IdInt
toLC _ (DFree v)   = Var v
toLC _ (DBound v)  = Var (IdInt v)
toLC _ (DLam _)    = error "toLC: argument not in normal form"
toLC n (DApp l r)  = App (toLC n l) (toLC n r)
toLC n (DCont t x) = Lam (IdInt n) $ toLC (n+1) (dbnf (DFree (IdInt n) : x) t)

-- Convert to DB form. The variables are looked up in a dictionary
-- (we use a list here) to find the de Bruijn index.
fromLC :: [IdInt] -> LC IdInt -> DB IdInt
fromLC vs (Var v) = case elemIndex v vs of
                        Just idx -> DBound idx
                        Nothing  -> DFree v
fromLC vs (Lam v t) = DLam $ fromLC (v:vs) t
fromLC vs (App l r) = DApp (fromLC vs l) (fromLC vs r)

\end{code}
