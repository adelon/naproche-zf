{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Syntax.LexicalPhrase where


import Base
import Syntax.Token (Token(..))

import Data.Char (isAlpha)
import Data.Text qualified as Text
import Text.Earley.Mixfix (Holey)
import Text.Earley (Grammar, Prod, (<?>), fullParses, parser, rule, token, satisfy)



-- | 'LexicalPhrase's should be nonempty lists with at least one proper word token.
-- Hyphens and quotes in words are treated as letters.
-- Thus /@manifold-with-boundary@/ is a singleton lexical phrase (one word).
--
type LexicalPhrase = Holey Token

-- MAYBE Add this instance by making LexicalPhrase a proper Type?
-- Until then we can use the default instance for lists of prettyprintable things.
--
-- instance Pretty LexicalPhrase where
--    pretty components = hsep (prettyComponent <$> components)
--       where
--          prettyComponent = \case
--             Nothing -> "_"
--             Just tok -> pretty tok



-- | Split data by grammatical number (singular/plural).
-- The 'Eq' and 'Ord' instances only consider the singular
-- form so that we can prefer known irregular plurals over
-- guessed irregular plurals when inserting items into
-- the 'Lexicon'.
data SgPl a
    = SgPl {sg :: a, pl :: a}
    deriving (Show, Functor, Generic, Hashable)

instance Eq a => Eq (SgPl a) where (==) = (==) `on` sg
instance Ord a => Ord (SgPl a) where compare = compare `on` sg


unsafeReadPhrase :: String -> LexicalPhrase
unsafeReadPhrase spec = case fst (fullParses (parser lexicalPhraseSpec) spec) of
    pat : _ -> pat
    _ -> error "unsafeReadPhrase failed"

unsafeReadPhraseSgPl :: String -> SgPl LexicalPhrase
unsafeReadPhraseSgPl spec = case fst (fullParses (parser lexicalPhraseSpecSgPl) spec) of
    pat : _ -> pat
    _ -> error "unsafeReadPhraseSgPl failed"


lexicalPhraseSpec :: Grammar r (Prod r String Char LexicalPhrase)
lexicalPhraseSpec = do
    hole     <- rule $ Nothing <$ token '?' <?> "hole"
    word     <- rule $ Just <$> many (satisfy (\c -> isAlpha c || c == '-'))
    space    <- rule $ Just . (:[]) <$> token ' '
    segment  <- rule $ hole <|> word
    rule $ (\s ss -> makePhrase (s:ss)) <$> segment <*> many (space *> segment)
    where
        makePhrase :: [Maybe String] -> LexicalPhrase
        makePhrase pat = fmap makeWord pat


lexicalPhraseSpecSgPl :: Grammar r (Prod r String Char (SgPl LexicalPhrase))
lexicalPhraseSpecSgPl = do
    space <- rule $ Just . (:[]) <$> token ' '
    hole  <- rule $ (Nothing, Nothing) <$ token '?'<?> "hole"

    word <- rule (many (satisfy isAlpha) <?> "word")
    wordSgPl <- rule $ (,) <$> (token '[' *> word) <* token '/' <*> word <* token ']'
    complexWord <- rule $ (\(a,b) -> (Just a, Just b)) . fuse <$>
        many ((<>) <$> (dup <$> word) <*> wordSgPl) <?> "word"
    segment  <- rule (hole <|> (dup . Just <$> word) <|> complexWord )
    rule $ (\s ss -> makePhrase (s:ss)) <$> segment <*> many (space *> segment)
    where
        dup x = (x,x)
        fuse = \case
            (a, b) : (c, d) : rest -> fuse ((a <> c, b <> d) : rest)
            [(a, b)] -> (a, b)
            _ -> error "Syntax.Abstract.fuse"

        makePhrase :: [(Maybe String, Maybe String)] -> SgPl LexicalPhrase
        makePhrase = (\(patSg, patPl) -> SgPl (fmap makeWord patSg) (fmap makeWord patPl)) . unzip

makeWord :: Maybe String -> Maybe Token
makeWord = fmap (Word . Text.pack)
