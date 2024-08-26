{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- This module defines the lexer and its associated data types.
-- The lexer takes `Text` as input and produces a stream of tokens
-- annotated with positional information. This information is bundled
-- together with the original raw input for producing error messages.
--
-- The lexer perfoms some normalizations to make describing the grammar easier.
-- Words outside of math environments are case-folded. Some commands are analysed
-- as variable tokens and are equivalent to their respective unicode variants
-- (α, β, γ, ..., 𝔸, 𝔹, ℂ, ...). Similarly, @\\begin{...}@ and @\\end{...}@ commands
-- are each parsed as single tokens.
--
module Syntax.Token
    ( Token(..)
    , tokToString
    , tokToText
    , TokStream(..)
    , Located(..)
    , runLexer
    ) where


import Base hiding (many)

import Control.Monad.Combinators
import Control.Monad.State.Strict
import Data.Char (isAsciiLower, isDigit)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Prettyprinter (Pretty(..))
import Text.Megaparsec hiding (Token, Label, label)
import Text.Megaparsec.Char qualified as Char
import Text.Megaparsec.Char.Lexer qualified as Lexer


runLexer :: String -> Text -> Either (ParseErrorBundle Text Void) [Located Token]
runLexer file raw = runParser (evalStateT toks initLexerState) file raw


type Lexer = StateT LexerState (Parsec Void Text)


data LexerState = LexerState
    { textNesting :: !Int
    -- ^ Represents nesting of braces inside of the @\text{...}@
    -- command. When we encounter @\text@ the token mode switches
    -- to text tokens. In order to switch back to math mode correctly
    -- we need to count the braces.
    , mode :: !Mode
    } deriving (Show, Eq)

initLexerState :: LexerState
initLexerState = LexerState 0 TextMode

incrNesting, decrNesting :: LexerState -> LexerState
incrNesting (LexerState n m) = LexerState (succ n) m
decrNesting (LexerState n m) = LexerState (pred n) m

data Mode = TextMode | MathMode deriving (Show, Eq)

isTextMode, isMathMode :: Lexer Bool
isTextMode = do
    m <- gets mode
    pure (m == TextMode)
isMathMode = do
    m <- gets mode
    pure (m == MathMode)

setTextMode, setMathMode :: Lexer ()
setTextMode = do
    st <- get
    put st{mode = TextMode}
setMathMode = do
    st <- get
    put st{mode = MathMode}

-- |
-- A token stream as input stream for a parser. Contains the raw input
-- before tokenization as 'Text' for showing error messages.
--
data TokStream = TokStream
    { rawInput :: !Text
    , unTokStream :: ![Located Token]
    } deriving (Show, Eq)

instance Semigroup TokStream where
    TokStream raw1 toks1 <> TokStream raw2 toks2 = TokStream (raw1 <> raw2) (toks1 <> toks2)

instance Monoid TokStream where
    mempty = TokStream mempty mempty

-- | A LaTeX token.
-- Invisible delimiters 'InvisibleBraceL' and 'InvisibleBraceR' are
-- unescaped braces used for grouping in TEX (@{@),
-- visibles braces are escaped braces (@\\{@).
data Token
    = Word !Text
    | Variable !Text
    | Symbol !Text
    | Integer !Int
    | Command !Text
    | Label Text -- ^ A /@\\label{...}@/ command (case-sensitive).
    | Ref (NonEmpty Text) -- ^ A /@\\ref{...}@/ command (case-sensitive).
    | BeginEnv !Text
    | EndEnv !Text
    | ParenL | ParenR
    | BracketL | BracketR
    | VisibleBraceL | VisibleBraceR
    | InvisibleBraceL | InvisibleBraceR
    deriving (Show, Eq, Ord, Generic, Hashable)

instance IsString Token where
    fromString w = Word (Text.pack w)

tokToText :: Token -> Text
tokToText = \case
    Word w -> w
    Variable v -> v
    Symbol s -> s
    Integer n -> Text.pack (show n)
    Command cmd -> Text.cons '\\' cmd
    Label m -> "\\label{" <> m <> "}"
    Ref ms -> "\\ref{" <> Text.intercalate ", " (toList ms) <> "}"
    BeginEnv "math" -> "$"
    EndEnv "math" -> "$"
    BeginEnv env -> "\\begin{" <> env <> "}"
    EndEnv env -> "\\end{" <> env <> "}"
    ParenL -> "("
    ParenR -> ")"
    BracketL -> "["
    BracketR -> "]"
    VisibleBraceL -> "\\{"
    VisibleBraceR -> "\\}"
    InvisibleBraceL -> "{"
    InvisibleBraceR -> "}"

tokToString :: Token -> String
tokToString = Text.unpack . tokToText

instance Pretty Token where
    pretty = \case
        Word w -> pretty w
        Variable v -> pretty v
        Symbol s -> pretty s
        Integer n -> pretty n
        Command cmd -> "\\" <> pretty cmd
        Label m -> "\\label{" <> pretty m <> "}"
        Ref m -> "\\ref{" <> pretty m <> "}"
        BeginEnv env -> "\\begin{" <> pretty env <> "}"
        EndEnv env -> "\\end{" <> pretty env <> "}"
        ParenL -> "("
        ParenR -> ")"
        BracketL -> "["
        BracketR -> "]"
        VisibleBraceL -> "\\{"
        VisibleBraceR -> "\\}"
        InvisibleBraceL -> "{"
        InvisibleBraceR -> "}"


data Located a = Located
    { startPos :: !SourcePos
    , unLocated :: !a
    , postWhitespace :: Whitespace
    } deriving (Show)

data Whitespace = NoSpace | Space deriving (Show)

collapseWhitespace :: [Whitespace] -> Whitespace
collapseWhitespace = \case
    Space : _ -> Space
    NoSpace : ws -> collapseWhitespace ws
    [] -> NoSpace

instance Eq a  => Eq  (Located a) where (==) = (==) `on` unLocated
instance Ord a => Ord (Located a) where compare = compare `on` unLocated


-- | Parses tokens, switching tokenizing mode when encountering math environments.
toks :: Lexer [Located Token]
toks = whitespace *> goNormal id <* eof
    where
        goNormal f = do
            r <- optional tok
            case r of
                Nothing -> pure (f [])
                Just t@Located{unLocated = BeginEnv "math"} -> goMath (f . (t:))
                Just t@Located{unLocated = BeginEnv "align*"} -> goMath (f . (t:))
                Just t@Located{unLocated = BeginEnv "cases"} -> goMath (f . (t:))
                Just t -> goNormal (f . (t:))
        goText f = do
            r <- optional textToken
            case r of
                Nothing -> pure (f [])
                Just t@Located{unLocated = BeginEnv "math"} -> goMathInText (f . (t:))
                Just t@Located{unLocated = EndEnv "text"} -> goMath (f . (t:))
                Just t@Located{unLocated = EndEnv "explanation"} -> goMath (f . (t:))
                Just t -> goText (f . (t:))
        goMath f = do
            r <- optional mathToken
            case r of
                Nothing -> pure (f [])
                Just t@Located{unLocated = EndEnv "math"} -> goNormal (f . (t:))
                Just t@Located{unLocated = EndEnv "align*"} -> goNormal (f . (t:))
                Just t@Located{unLocated = EndEnv "cases"} -> goNormal (f . (t:))
                Just t@Located{unLocated = BeginEnv "text"} -> goText (f . (t:))
                Just t@Located{unLocated = BeginEnv "explanation"} -> goText (f . (t:))
                Just t -> goMath (f . (t:))
        goMathInText f = do
            r <- optional mathToken
            case r of
                Nothing -> pure (f [])
                Just t@(Located{unLocated = EndEnv "math"}) -> goText (f . (t:))
                Just t@(Located{unLocated = BeginEnv "text"}) -> goText (f . (t:))
                Just t -> goMathInText (f . (t:))
{-# INLINE toks #-}

-- | Parses a single normal mode token.
tok :: Lexer (Located Token)
tok =
    word <|> var <|> symbol <|> mathBegin <|> alignBegin <|> casesBegin <|> begin <|> end <|> opening <|> closing <|> label <|> ref <|> command

-- | Parses a single math mode token.
mathToken :: Lexer (Located Token)
mathToken =
    var <|> symbol <|> number <|> begin <|> alignEnd <|> casesEnd <|> end <|> opening <|> closing <|> beginText <|> beginExplanation <|> mathEnd <|> command

beginText :: Lexer (Located Token)
beginText = lexeme do
    Char.string "\\text{" <|> Char.string "\\textbox{"
    setTextMode
    pure (BeginEnv "text")

-- | Same as text modulo spacing, so we treat it synonymously
beginExplanation :: Lexer (Located Token)
beginExplanation = lexeme do
    Char.string "\\explanation{"
    setTextMode
    pure (BeginEnv "text")

-- | Normal mode embedded into math mode via @\text{...}@.
textToken :: Lexer (Located Token)
textToken = word <|> symbol <|> begin <|> end <|> textEnd <|> mathBegin <|> alignBegin <|> opening' <|> closing' <|> ref <|> command
    where
        textEnd = lexeme do
            0 <- gets textNesting -- Otherwise fail.
            Char.char '}'
            setMathMode
            pure (EndEnv "text")

        opening' = lexeme (group <|> optional (Char.string "\\left") *> (brace <|> paren <|> bracket))
            where
                brace = VisibleBraceL <$ lexeme (Char.string "\\{")
                group = InvisibleBraceL <$ lexeme (Char.char '{') <* modify' incrNesting
                paren = ParenL <$ lexeme (Char.char '(')
                bracket = BracketL <$ lexeme (Char.char '[')

        closing' = lexeme (group <|> optional (Char.string "\\right") *> (brace <|> paren <|> bracket))
            where
                brace = VisibleBraceR <$ lexeme (Char.string "\\}")
                group = InvisibleBraceR <$ lexeme (Char.char '}') <* modify' decrNesting
                paren = ParenR <$ lexeme (Char.char ')')
                bracket = BracketR <$ lexeme (Char.char ']')


-- | Parses a single begin math token.
mathBegin :: Lexer (Located Token)
mathBegin = guardM isTextMode *> lexeme do
    Char.string "\\(" <|> Char.string "\\[" <|> Char.string "$"
    setMathMode
    pure (BeginEnv "math")

alignBegin :: Lexer (Located Token)
alignBegin = guardM isTextMode *> lexeme do
    Char.string "\\begin{align*}"
    setMathMode
    pure (BeginEnv "align*")

casesBegin :: Lexer (Located Token)
casesBegin = guardM isTextMode *> lexeme do
    Char.string "\\begin{cases}"
    setMathMode
    pure (BeginEnv "cases")

-- | Parses a single end math token.
mathEnd :: Lexer (Located Token)
mathEnd = guardM isMathMode *> lexeme do
    Char.string "\\)" <|> Char.string "\\]" <|> Char.string "$"
    setTextMode
    pure (EndEnv "math")

alignEnd :: Lexer (Located Token)
alignEnd = guardM isMathMode *> lexeme do
    Char.string "\\end{align*}"
    setTextMode
    pure (EndEnv "align*")

casesEnd :: Lexer (Located Token)
casesEnd = guardM isMathMode *> lexeme do
    Char.string "\\end{cases}"
    setTextMode
    pure (EndEnv "cases")


-- | Parses a word. Words are returned casefolded, since we want to ignore their case later on.
word :: Lexer (Located Token)
word = guardM isTextMode *> lexeme do
    w <- some (Char.letterChar <|> Char.char '\'' <|> Char.char '-')
    let t = Word (Text.toCaseFold (Text.pack w))
    pure t

number :: Lexer (Located Token)
number = lexeme $ Integer <$> Lexer.decimal


var :: Lexer (Located Token)
var = guardM isMathMode *> lexeme (fmap Variable var')
    where
    var' = do
        alphabeticPart <- letter <|> bb <|> greek
        variationPart  <- subscriptNumber <|> ticked <|> pure ""
        pure (alphabeticPart <> variationPart)

    subscriptNumber :: Lexer Text
    subscriptNumber = do
        Char.char '_'
        n <- some Char.digitChar
        pure (Text.pack n)

    -- Temporary hack to fit the TPTP format.
    ticked :: Lexer Text
    ticked = do
        ticks <- some $ Char.char '\''
        let ticks' = "prime" <$ ticks :: [Text]
        pure (Text.concat ticks')

    letter :: Lexer Text
    letter = fmap Text.singleton Char.letterChar

    greek :: Lexer Text
    greek = try do
        Char.char '\\'
        l <- symbolParser greeks
        notFollowedBy Char.letterChar
        pure l

    greeks :: [Text]
    greeks =
        [ "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"
        , "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", "sigma"
        , "tau", "upsilon", "phi", "chi", "psi", "omega"
        , "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon"
        , "Phi", "Psi", "Omega"
        ]

    bb :: Lexer Text
    bb = do
        Char.string "\\mathbb{"
        l <-  symbolParser bbs
        Char.char '}'
        pure $ "bb" <> l

    bbs :: [Text]
    bbs = Text.singleton <$> ['A'..'Z']


    symbolParser :: [Text] -> Lexer Text
    symbolParser symbols = asum (fmap Char.string symbols)


symbol :: Lexer (Located Token)
symbol = lexeme do
    symb <- some (satisfy (`elem` symbols))
    pure (Symbol (Text.pack symb))
        where
        symbols :: [Char]
        symbols = ".,:;!?@=≠+-/|^><≤≥*&≈⊂⊃⊆⊇∈“”‘’"

-- | Parses a TEX-style command.
command :: Lexer (Located Token)
command = lexeme do
    Char.char '\\'
    cmd <- some Char.letterChar
    pure (Command (Text.pack cmd))

-- | Parses the beginning of an environment.
-- Commits only after having seen "\begin{".
begin :: Lexer (Located Token)
begin = lexeme do
    Char.string "\\begin{"
    env <- some (Char.letterChar <|> Char.char '*')
    Char.char '}'
    pure (BeginEnv (Text.pack env))

-- | Parses a label command and extracts its marker.
label :: Lexer (Located Token)
label = lexeme do
    Char.string "\\label{"
    m <- marker
    Char.char '}'
    pure (Label m)

-- | Parses a label command and extracts its marker.
ref :: Lexer (Located Token)
ref = lexeme do
    -- @\\cref@ is from @cleveref@ and @\\hyperref@ is from @hyperref@
    cmd <- Char.string "\\ref{" <|> Char.string "\\cref{" <|> Char.string "\\hyperref["
    ms <- NonEmpty.fromList <$> marker `sepBy1` Char.char ','
    case cmd of
        "\\hyperref[" -> Char.string "]{" *> some (satisfy (/= '}')) *> Char.char '}' *> pure (Ref ms)
        _ -> Char.char '}' *> pure (Ref ms)

marker :: Lexer Text
marker = do
    c <- satisfy isAsciiLower
    cs <- takeWhileP Nothing (\x -> isAsciiLower x || isDigit x || x == '_')
    pure (Text.cons c cs)

-- | Parses the end of an environment.
-- Commits only after having seen "\end{".
end :: Lexer (Located Token)
end = lexeme do
    Char.string "\\end{"
    env <- some (Char.letterChar <|> Char.char '*')
    Char.char '}'
    pure (EndEnv (Text.pack env))

-- | Parses an opening delimiter.
opening :: Lexer (Located Token)
opening = lexeme (group <|> optional (Char.string "\\left") *> (paren <|> brace <|> bracket))
    where
        brace = VisibleBraceL <$ lexeme (Char.string "\\{")
        group = InvisibleBraceL <$ lexeme (Char.char '{')
        paren = ParenL <$ lexeme (Char.char '(')
        bracket = BracketL <$ lexeme (Char.char '[')

-- | Parses a closing delimiter.
closing :: Lexer (Located Token)
closing = lexeme (group <|> optional (Char.string "\\right") *> (paren <|> brace <|> bracket))
    where
        brace = VisibleBraceR <$ lexeme (Char.string "\\}")
        group = InvisibleBraceR <$ lexeme (Char.char '}')
        paren = ParenR <$ lexeme (Char.char ')')
        bracket = BracketR <$ lexeme (Char.char ']')

-- | Turns a Lexer into one that tracks the source position of the token
-- and consumes trailing whitespace.
lexeme :: Lexer a -> Lexer (Located a)
lexeme p = do
    start <- getSourcePos
    t <- p
    w <- whitespace
    pure (Located start t w)

space :: Lexer Whitespace
space = Space <$ (Char.char ' ' <|> Char.char '\n' <|> Char.char '\r')
    <|> Space <$ (Char.string "\\ " <|> Char.string "\\\\" <|> Char.string "\\!" <|> Char.string "\\," <|> Char.string "\\:" <|> Char.string "\\;" <|> Char.string "\\;")

whitespace :: Lexer Whitespace
whitespace = do
    ws <- many (spaces <|> comment)
    pure (collapseWhitespace ws)
    where
        spaces = collapseWhitespace <$> some space
        comment = NoSpace <$ Lexer.skipLineComment "%"
