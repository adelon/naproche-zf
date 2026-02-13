{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

module Report.Location where

import Base
import Text.Megaparsec.Pos (SourcePos (sourceColumn, sourceLine), unPos)
import Data.Bits
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Word (Word16)
import System.IO.Unsafe (unsafePerformIO)

-- | File identifier used in packed source locations.
newtype FileId = FileId
    { unFileId :: Word16
    } deriving stock (Show, Eq, Ord, Generic)
      deriving anyclass (Hashable)

-- | Packed source location.
-- Bit layout (high to low):
-- 16 bits file id | 24 bits line | 24 bits column.
newtype Location = Location
    { unLocation :: Word64
    } deriving stock (Eq, Ord, Generic)
      deriving anyclass (Hashable)

data FileRegistry = FileRegistry
    { pathToFileId :: Map FilePath FileId
    , fileIdToPath :: IntMap FilePath
    , nextFileId :: {-# UNPACK #-} !Word16
    }

initialFileRegistry :: FileRegistry
initialFileRegistry = FileRegistry
    { pathToFileId = mempty
    , fileIdToPath = mempty
    , nextFileId = 0
    }

fileRegistryRef :: IORef FileRegistry
fileRegistryRef = unsafePerformIO (newIORef initialFileRegistry)
{-# NOINLINE fileRegistryRef #-}

registerFilePath :: MonadIO io => FilePath -> io FileId
registerFilePath path = liftIO $
    atomicModifyIORef' fileRegistryRef \registry ->
        case Map.lookup path (pathToFileId registry) of
            Just fileId ->
                (registry, fileId)
            Nothing ->
                if nextFileId registry == maxBound
                    then error "registerFilePath: exhausted file-id space (16 bits)"
                    else
                        let fileId = FileId (nextFileId registry)
                            fileIdInt = fromIntegral (unFileId fileId)
                            registry' = FileRegistry
                                { pathToFileId = Map.insert path fileId (pathToFileId registry)
                                , fileIdToPath = IntMap.insert fileIdInt path (fileIdToPath registry)
                                , nextFileId = nextFileId registry + 1
                                }
                        in
                            (registry', fileId)

lookupFilePath :: FileId -> Maybe FilePath
lookupFilePath fileId = unsafePerformIO do
    registry <- readIORef fileRegistryRef
    pure (IntMap.lookup (fromIntegral (unFileId fileId)) (fileIdToPath registry))

fileShift, lineShift :: Int
fileShift = 48
lineShift = 24

fileMask, coordMask :: Word64
fileMask = 0xFFFF
coordMask = 0xFFFFFF

nowhereWord :: Word64
nowhereWord = maxBound

mkLocation :: FileId -> Int -> Int -> Location
mkLocation fileId line column =
    if lineWord > coordMask || columnWord > coordMask
        then error ("mkLocation: line/column out of range (line=" <> show line <> ", column=" <> show column <> ")")
        else
            Location
                (   (fromIntegral (unFileId fileId) `shiftL` fileShift)
                 .|. (lineWord `shiftL` lineShift)
                 .|. columnWord
                )
    where
        lineWord = fromIntegral line :: Word64
        columnWord = fromIntegral column :: Word64

locFileId :: Location -> Maybe FileId
locFileId (Location w)
    | w == nowhereWord = Nothing
    | otherwise = Just (FileId (fromIntegral ((w `shiftR` fileShift) .&. fileMask)))

locFile :: Location -> FilePath
locFile loc = case locFileId loc of
    Nothing -> "<nowhere>"
    Just fileId ->
        fromMaybe ("<file#" <> show (unFileId fileId) <> ">") (lookupFilePath fileId)

locLine :: Location -> Int
locLine (Location w)
    | w == nowhereWord = -1
    | otherwise = fromIntegral ((w `shiftR` lineShift) .&. coordMask)

locColumn :: Location -> Int
locColumn (Location w)
    | w == nowhereWord = -1
    | otherwise = fromIntegral (w .&. coordMask)

instance Show Location where
    showsPrec p loc =
        showParen (p > appPrec) $
            showString "Location {locFile = "
            . shows (locFile loc)
            . showString ", locLine = "
            . shows (locLine loc)
            . showString ", locColumn = "
            . shows (locColumn loc)
            . showString "}"
      where
        appPrec = 10

fromSourcePos :: FileId -> SourcePos -> Location
fromSourcePos fileId pos = mkLocation
    fileId
    (unPos (sourceLine pos))
    (unPos (sourceColumn pos))

prettyLocation :: Location -> String
prettyLocation loc =
    locFile loc <> " " <> show (locLine loc) <> ":" <> show (locColumn loc)

locationToText :: Location -> Text
locationToText loc = Text.pack (prettyLocation loc)

-- | Things that have a location.
class Locatable a where
    locate :: a -> Location

pattern Nowhere :: Location
pattern Nowhere = Location 0xFFFFFFFFFFFFFFFF

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
