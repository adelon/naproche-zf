module Serial (Serial, start, next) where

import Data.Eq
import Data.Hashable
import Data.Ord
import GHC.Generics as Export (Generic(..))
import Numeric.Natural
import Prelude (Num(..))
import Text.Show


newtype Serial = Serial Natural deriving (Show, Eq, Ord, Generic, Hashable)

start :: Serial
start = Serial 0

next :: Serial -> Serial
next (Serial k) = Serial (k + 1)
