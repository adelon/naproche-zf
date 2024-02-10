{-# LANGUAGE NoImplicitPrelude #-}


module Version (info, infoBuilder) where

import Data.Functor
import Data.Semigroup
import Data.Text (Text)
import Data.Version
import Paths_zf qualified as ZF
import Text.Builder


-- | Informational text about the version number (extracted from the cabal file).
info :: Text
info = run infoBuilder

infoBuilder :: Builder
infoBuilder = text "Version " <> versionToBuilder ZF.version

versionToBuilder :: Version -> Builder
versionToBuilder ver = intercalate (char '.') (decimal <$> versionBranch ver)
