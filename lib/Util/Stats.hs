module Util.Stats where

import Control.Monad.Except
import Control.Monad.State
import Util.IdInt

data Stats = Stats {numSubsts :: Int} deriving (Eq, Ord, Show)

type M = ExceptT String (State Stats)

type FM = StateT IdInt M

count :: M ()
count = lift $ modify (\s -> s {numSubsts = numSubsts s + 1})

countFM :: FM ()
countFM = lift count

done :: M a
done = throwError "Out of gas!"

doneFM :: FM a
doneFM = lift done

runM :: M a -> Maybe (Stats, a)
runM ma =
  let (result, subCount) = runState (runExceptT ma) (Stats 0)
   in case result of
        Left s -> Nothing
        Right x -> Just (subCount, x)

runF :: FM a -> IdInt -> M a 
runF ma x = evalStateT ma x