{-# LANGUAGE DeriveAnyClass #-}

module Report.Location where

import Base
import Text.Megaparsec.Pos (SourcePos, sourceName, sourceLine, unPos)
import Data.Text qualified as Text

data Location = Location
    { locFile :: !FilePath
    , locLine :: {-# UNPACK #-} !Int
    , locColumn :: {-# UNPACK #-} !Int
    } deriving (Show, Eq, Ord, Generic, Hashable)


fromSourcePos :: SourcePos -> Location
fromSourcePos pos = Location
    { locFile = sourceName pos
    , locLine = unPos (sourceLine pos)
    , locColumn = unPos (sourceLine pos)
    }

prettyLocation :: Location -> String
prettyLocation loc =
    locFile loc <> ": " <> show (locLine loc) <> ":" <> show (locColumn loc)

locationToText :: Location -> Text
locationToText loc = Text.pack (prettyLocation loc)

-- | Things that have a location.
class Locatable a where
    locate :: a -> Location

pattern Nowhere :: Location
pattern Nowhere = Location "<nowhere>" (-1) (-1)

instance Locatable Location where
    locate = id

instance Locatable a => Locatable [a] where
    locate []    = Nowhere
    locate (x:_) = locate x

instance Locatable a => Locatable (Maybe a) where
    locate Nothing  = Nowhere
    locate (Just x) = locate x

instance Locatable a => Locatable (NonEmpty a) where
    locate (x :| _) = locate x
