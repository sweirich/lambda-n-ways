-- | A fast type of identifiers, Ints, for $\lambda$-expressions.
module Util.IdInt
  ( IdInt (..),
    firstBoundId,
    FreshM,
    convVar,
    newId,
  )
where

import Data.List (union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S
import Util.Imports

-- | An IdInt is just another name for an Int. We only use the nonnegative Ints though
newtype IdInt = IdInt Int
  deriving (Eq, Ord, Generic, Num)

instance NFData IdInt

-- It is handy to make IdInt enumerable.
instance Enum IdInt where
  toEnum i = IdInt i
  fromEnum (IdInt i) = i

-- 0 is the smallest identifier
firstBoundId :: IdInt
firstBoundId = toEnum 0

-- We show IdInts so they look like variables.

instance Show IdInt where
  show (IdInt i) = "x" ++ show i

instance Read IdInt where
  -- skip "x" then read int
  readsPrec _ (_ : str) = coerce ((readsPrec 0 str) :: [(Int, String)])
  readsPrec _ [] = error "no parse IdInt"

-- Generating IdInts

-- Only generate positive idint

instance Arbitrary IdInt where
  arbitrary = IdInt <$> arbitrarySizedNatural
  shrink (IdInt 0) = []
  shrink (IdInt n) = [IdInt (n -1)]

-- Converting IdInts

-- Find a new identifier not in a given set

-- The state monad has the next unused Int and a mapping of identifiers
-- to IdInt.

type FreshM v a = State (Int, M.Map v IdInt) a

-- The only operation we do in the monad is to convert a variable.
-- If the variable is in the map the use it, otherwise add it.

convVar :: (Ord v) => v -> FreshM v IdInt
convVar v = do
  (i, m) <- get
  case M.lookup v m of
    Nothing -> do
      let ii = toEnum i
      put (i + 1, M.insert v ii m)
      return ii
    Just ii -> return ii

newId :: S.Set IdInt -> IdInt
newId s = if S.null s then firstBoundId else succ (S.findMax s)

--newId :: [IdInt] -> IdInt
--newId [] = firstBoundId
--newId vs = succ (maximum vs)
