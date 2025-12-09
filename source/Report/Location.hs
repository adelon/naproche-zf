module Report.Location where

import Base
import Text.Megaparsec.Pos



class Locatable a where
    locate :: a -> SourcePos

nowhere :: SourcePos
nowhere = initialPos "Nowhere"

instance Locatable SourcePos where
    locate = id

instance Locatable a => Locatable [a] where
    locate []    = nowhere
    locate (x:_) = locate x

instance Locatable a => Locatable (Maybe a) where
    locate Nothing  = nowhere
    locate (Just x) = locate x

instance Locatable a => Locatable (NonEmpty a) where
    locate (x :| _) = locate x
