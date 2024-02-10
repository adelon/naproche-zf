module Checking.Cache where

import Base
import Syntax.Internal(Task)

import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Binary

-- The following would not work:
-- Checking that the new task is a superset of an old task:
-- additional assumptions may slow down the checking and
-- lead to a failure with default timeouts. Then when you
-- recheck the file from scratch it won't work.


hashTasks :: [Task] -> IntSet
hashTasks tasks = IntSet.fromList (hash <$> tasks)


putTaskCache :: MonadIO io => FilePath -> [Task] -> io ()
putTaskCache path tasks = liftIO $ encodeFile path $ hashTasks tasks


notInCache :: MonadIO io => FilePath -> Task -> io Bool
notInCache path task = do
    eitherHashedTasks <- liftIO $ decodeFileOrFail path
    pure case eitherHashedTasks of
        Left _ -> True
        Right hashedTasks -> hash task `IntSet.notMember` hashedTasks
