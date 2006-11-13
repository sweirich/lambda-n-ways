\begin{code}

{-
 - Alternative De Bruijn index based lambda calculus interpreter
 - 
 - Author: Bertram Felgenhauer <int-e@gmx.de>
 -}

module DeBruijnC (nf) where

import Lambda
import IdInt
import Data.List

data DB v = DFree v              -- free variable
          | DBound Int           -- bound variable, uses de Bruijn index
          | DLam (DB v)          -- lambda abstraction (unbound)
          | DApp (DB v) (DB v)   -- application
          | DCont (DB v) [DB v]  -- lambda abstraction (bound to a context)

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
