{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ApplicativeDo #-}


module Syntax.Import where


import Base

import Text.Regex.Applicative.Text
import Data.CharSet qualified as CharSet
import Data.Char (isAlphaNum)

gatherImports :: Text -> [FilePath]
gatherImports s = case findFirstPrefix imps s of
    Nothing -> []
    Just (paths, _) -> paths


imps :: RE Char [FilePath]
imps = do
    mpath <- optional imp
    paths <- many (few anySym *> string "\n" *> imp)
    few anySym
    begin
    pure case mpath of
        Nothing -> paths
        Just path -> path : paths


imp :: RE Char FilePath
imp = do
    -- Requiring a newline makes it possible to comment imports out.
    string "\\import{"
    path <- few (psym isTheoryNameChar)
    sym '}'
    pure path

isTheoryNameChar :: Char -> Bool
isTheoryNameChar c = isAlphaNum c || c `CharSet.member` CharSet.fromList ".-_/"

begin :: RE Char Text
begin = string "\\begin{"
