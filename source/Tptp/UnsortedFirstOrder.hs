{-# LANGUAGE NoImplicitPrelude #-}

-- | Helpers for building TPTP FOF syntax.
module Tptp.UnsortedFirstOrder where

import Base
import Data.Char
import Data.Text qualified as Text
import TextBuilder


isAsciiLetter :: Char -> Bool
isAsciiLetter c = isAsciiLower c || isAsciiUpper c

isAsciiAlphaNumOrUnderscore :: Char -> Bool
isAsciiAlphaNumOrUnderscore c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'


-- | A TPTP atomic word, starting with a lowercase letter or enclosed in single quotes.
newtype AtomicWord = AtomicWord Text deriving (Show, Eq, Ord, IsString)

isProperAtomicWord :: Text -> Bool
isProperAtomicWord w = case Text.uncons w of
    Nothing -> False
    Just (head, tail) -> isAsciiLower head && Text.all isAsciiAlphaNumOrUnderscore tail

-- | A TPTP variable, written as a word starting with an uppercase letter.
newtype Variable = Variable Text deriving (Show, Eq, Ord, IsString)

isVariable :: Text -> Bool
isVariable var = case Text.uncons var of
    Nothing -> False -- Variables must be nonempty.
    Just (head, tail) -> isAsciiUpper head && Text.all isAsciiAlphaNumOrUnderscore tail


data Role
    = Axiom
    | AxiomUseful -- ^ Annotated axiom for trainig premise selection.
    | AxiomRedundant -- ^ Annotated axiom for trainig premise selection.
    | Hypothesis
    | Conjecture
    | NegatedConjecture
    deriving (Show, Eq, Ord)

data Name = NameAtomicWord AtomicWord | NameInt Int
    deriving (Show, Eq, Ord)

newtype Source = Source Text deriving (Show, Eq, Ord)

data AnnotatedFormula
    = AnnotatedFormula Name Role TextBuilder Source

newtype Task
    = Task [AnnotatedFormula]
    deriving (Semigroup, Monoid)

instance Eq AnnotatedFormula where
    AnnotatedFormula name role phi src == AnnotatedFormula name' role' phi' src' =
        (name, role, src, TextBuilder.toText phi) == (name', role', src', TextBuilder.toText phi')

instance Ord AnnotatedFormula where
    compare (AnnotatedFormula name role phi src) (AnnotatedFormula name' role' phi' src') =
        compare (name, role, src, TextBuilder.toText phi) (name', role', src', TextBuilder.toText phi')

instance Show AnnotatedFormula where
    show (AnnotatedFormula name role phi src) =
        "AnnotatedFormula " <> show name <> " " <> show role <> " " <> show (TextBuilder.toText phi) <> " " <> show src

instance Eq Task where
    Task xs == Task ys = xs == ys

instance Ord Task where
    compare (Task xs) (Task ys) = compare xs ys

instance Show Task where
    show (Task fofs) = "Task " <> show fofs

toTextNewline :: Task -> Text
toTextNewline task = TextBuilder.toText (buildTask task <> char '\n')

toText :: Task -> Text
toText task = TextBuilder.toText (buildTask task)

singleQuoted :: Text -> Text
singleQuoted str = Text.snoc (Text.cons '\'' (escape str)) '\''
    where
        -- First escape backslashes, then single quotes.
        escape :: Text -> Text
        escape = Text.replace "'" "\\'" . Text.replace "\\" "\\\\"

buildTuple :: [TextBuilder] -> TextBuilder
buildTuple bs = char '(' <> intercalate (char ',') bs <> char ')'

buildList :: [TextBuilder] -> TextBuilder
buildList bs = char '[' <> intercalate (char ',') bs <> char ']'

buildAtomicWord :: AtomicWord -> TextBuilder
buildAtomicWord (AtomicWord w) = text if isProperAtomicWord w then w else singleQuoted w

buildVariable :: Variable -> TextBuilder
buildVariable (Variable v) = text (Text.replace "'" "_" v)

buildName :: Name -> TextBuilder
buildName = \case
        NameAtomicWord w -> buildAtomicWord w
        NameInt n -> decimal n

buildRole :: Role -> TextBuilder
buildRole = \case
        Axiom -> "axiom"
        AxiomUseful -> "axiom_useful"
        AxiomRedundant -> "axiom_redundant"
        Hypothesis -> "hypothesis"
        Conjecture -> "conjecture"
        NegatedConjecture -> "negated_conjecture"

buildAnnotatedFormula :: AnnotatedFormula -> TextBuilder
buildAnnotatedFormula (AnnotatedFormula name role phi (Source src)) =
    let info = text (if Text.null src then "" else ",\"" <> src <> "\"")
    in  "fof(" <> intercalate (char ',') [buildName name, buildRole role, phi] <> info <> ")."

buildTask :: Task -> TextBuilder
buildTask (Task fofs) = intercalate (char '\n') (map buildAnnotatedFormula fofs)
