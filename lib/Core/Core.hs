module Core.Core where

import Core.Unique
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Util.IdInt
import Util.Syntax.Lambda

type Var = IdInt

type Id = IdInt

type CoreExpr = LC IdInt

type CoreBndr = IdInt

type CoreArg = CoreExpr

mkApps :: CoreExpr -> [CoreExpr] -> CoreExpr
mkApps f args = foldl' App f args

--mkVarApps :: CoreExpr -> [Var] -> CoreExpr
--mkVarApps f vars = foldl' (\ e a -> App e (varToCoreExpr a)) f vars

setVarUnique :: Var -> Unique -> Var
setVarUnique (IdInt _x) (MkUnique y) = IdInt y

{-
 combination of foldl with zip.  It works with equal length lists.
-}

foldl2 :: (acc -> a -> b -> acc) -> acc -> [a] -> [b] -> acc
foldl2 _ z [] [] = z
foldl2 k z (a : as) (b : bs) = foldl2 k (k z a b) as bs
foldl2 _ _ _ _ = error "Util: foldl2"

infixr 4 `orElse`

-- | Flipped version of @fromMaybe@, useful for chaining.
orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

isLocalVar :: Var -> Bool
isLocalVar = const True

isLocalId :: Var -> Bool
isLocalId = const True

isId :: Var -> Bool
isId = const True
