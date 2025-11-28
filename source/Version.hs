{-# LANGUAGE NoImplicitPrelude #-}


module Version (info, infoBuilder) where

import Data.Functor
import Data.Semigroup
import Data.Text (Text)
import Data.Version
import Paths_zf qualified as ZF
import TextBuilder


-- | Informational text about the version number (extracted from the cabal file).
info :: Text
info = toText infoBuilder

infoBuilder :: TextBuilder
infoBuilder = text "Version " <> versionToBuilder ZF.version

versionToBuilder :: Version -> TextBuilder
versionToBuilder ver = intercalate (char '.') (decimal <$> versionBranch ver)
