module Syntax.LexiconFile where

import Base hiding (many)
import Syntax.Adapt
import Syntax.LexicalPhrase
import Syntax.Abstract

import Data.Char (isAlphaNum, isAsciiLower, isLetter, isDigit)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Text.Earley.Mixfix (Holey)
import Text.Megaparsec hiding (Token, Label, label)
import Text.Megaparsec.Char qualified as Char
import UnliftIO.Directory
import System.FilePath

type LexiconFileParser = Parsec Void Text

parseLexiconFile :: IO [ScannedLexicalItem]
parseLexiconFile = do
    currentDir  <- getCurrentDirectory
    let csvPath = (currentDir </> "library" </> "lexicon.csv")
    csv <- Text.readFile csvPath
    case runParser lexiconFile csvPath csv of
        Left err -> fail (errorBundlePretty err)
        Right entries -> pure entries

lexiconFile :: LexiconFileParser [ScannedLexicalItem]
lexiconFile = many line <* eof

line :: LexiconFileParser ScannedLexicalItem
line = do
    c <- satisfy isAsciiLower
    cs <- takeWhileP Nothing (\x -> isAsciiLower x || isDigit x || x == '_')
    let marker = Marker (Text.cons c cs)
    Char.char ','
    kind <- takeWhile1P Nothing isLetter
    Char.char ','
    item <- case kind of
        "adj" -> do
            entry <- takeWhile1P Nothing (\x -> isAlphaNum x || x == '\'' || x == '-' || x == ' ')
            pure (ScanAdj (unsafeReadPhrase (Text.unpack entry)) marker)
        "rel" -> do
            entry <- tokenSingle
            pure (ScanRelationSymbol entry marker)
        "const" -> do
            entry <- tokenPattern
            pure (ScanFunctionSymbol entry marker)
        _ -> error "Unrecognized lexical item kind in lexicon file."
    optional Char.eol
    pure item

tokenSingle :: LexiconFileParser Token
tokenSingle = Command <$> (single '\\' *> takeWhile1P Nothing (\x -> isAlphaNum x))

-- TODO allow spaces
tokenPattern :: LexiconFileParser (Holey Token)
tokenPattern = some (Just <$> tokenSingle <|> Nothing <$ single '?')
