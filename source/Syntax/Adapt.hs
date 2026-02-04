{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

module Syntax.Adapt where

import Base
import Syntax.Abstract
import Syntax.Lexicon
import Syntax.Token
import Report.Location

import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Data.HashSet qualified as HS
import Data.HashMap.Strict qualified as HM
import Data.Text qualified as Text
import Text.Earley.Mixfix (Associativity(..))
import Text.Regex.Applicative

scanChunk :: [Located Token] -> [ScannedLexicalItem]
scanChunk ltoks =
    let toks = unLocated <$> ltoks
        matchOrErr re env pos = match re toks ?? error ("could not find lexical pattern in " <> env <> " at " <> prettyLocation pos)
    in case ltoks of
        Located{startPos = pos, unLocated = BeginEnv "definition"} : _ ->
            matchOrErr definition "definition" pos
        -- TODO Located{startPos = pos, unLocated = BeginEnv "signature"} : _ ->
        --    matchOrErr signatureExtension "signature" pos
        Located{startPos = pos, unLocated = BeginEnv "abbreviation"} : _ ->
            matchOrErr abbreviation "abbreviation" pos
        Located{startPos = pos, unLocated = (BeginEnv "struct")} :_ ->
            matchOrErr structRE "struct definition" pos
        Located{startPos = pos, unLocated = (BeginEnv "inductive")} :_ ->
            matchOrErr inductive "inductive definition" pos
        _ -> []

adaptChunks :: [[Located Token]] -> Lexicon -> Lexicon
adaptChunks = extendLexicon . concatMap scanChunk

data ScannedLexicalItem
    = ScanAdj LexicalPhrase Marker
    | ScanFun LexicalPhrase Marker
    | ScanNoun LexicalPhrase Marker
    | ScanStructNoun LexicalPhrase Marker
    | ScanVerb LexicalPhrase Marker
    | ScanRelationSymbol RelationSymbol Marker
    | ScanFunctionSymbol FunctionSymbol Marker
    | ScanPrefixPredicate PrefixPredicate Marker
    | ScanStructOp Text -- we an use the command text as export name.
    deriving (Show, Eq)

skipUntilNextLexicalEnv :: RE Token [Token]
skipUntilNextLexicalEnv = many (psym otherToken)
    where
        otherToken tok = tok /= BeginEnv "definition" && tok /= BeginEnv "struct" && tok /= BeginEnv "abbreviation"

notEndOfLexicalEnvToken :: RE Token Token
notEndOfLexicalEnvToken = psym innerToken
    where
        innerToken tok = tok /= EndEnv "definition" && tok /= EndEnv "struct" && tok /= EndEnv "abbreviation"

definition ::  RE Token [ScannedLexicalItem]
definition = do
    sym (BeginEnv "definition")
    few notEndOfLexicalEnvToken
    m <- labelRE
    few anySym
    lexicalItem <- headRE
    few anySym
    sym (EndEnv "definition")
    skipUntilNextLexicalEnv
    pure [lexicalItem m]

abbreviation ::  RE Token [ScannedLexicalItem]
abbreviation = do
    sym (BeginEnv "abbreviation")
    few anySym
    m <- labelRE
    few anySym
    lexicalItem <- headRE
    few anySym
    sym (EndEnv "abbreviation")
    skipUntilNextLexicalEnv
    pure [lexicalItem m]

signatureExtension ::  RE Token [ScannedLexicalItem]
signatureExtension = do
    sym (BeginEnv "signature")
    few notEndOfLexicalEnvToken
    m <- labelRE
    few anySym
    lexicalItem <- headRE
    few anySym
    sym (EndEnv "signature")
    skipUntilNextLexicalEnv
    pure [lexicalItem m]

signatureExtensionAtom ::  RE Token [ScannedLexicalItem]
signatureExtensionAtom = do
    sym (BeginEnv "signatureatom")
    few notEndOfLexicalEnvToken
    m <- labelRE
    few anySym
    lexicalItem <- sigPred
    few anySym
    sym (EndEnv "signatureatom")
    skipUntilNextLexicalEnv
    pure [lexicalItem m]

labelRE :: RE Token Marker
labelRE = msym \case
    Label m -> Just (Marker m)
    _ -> Nothing

-- | 'RE' that matches the head of a definition.
headRE :: RE Token (Marker -> ScannedLexicalItem)
-- Note that @<|>@ is left biased for 'RE', so we can just
-- place 'adj' before 'verb' and do not have to worry about
-- overlapping patterns.
headRE = ScanNoun <$> nounRE
    <|> ScanAdj <$> adjRE
    <|> ScanVerb <$> verbRE
    <|> ScanFun <$> funRE
    <|> ScanRelationSymbol . fst <$> relationSymbolRE
    <|> ScanFunctionSymbol <$> functionSymbolRE
    <|> ScanPrefixPredicate <$> prefixPredicate

sigPred :: RE Token (Marker -> ScannedLexicalItem)
sigPred = ScanNoun . toLexicalPhrase <$> (math var *> can *> be *> an *> pat <* iff)
    <|> ScanAdj . toLexicalPhrase <$> (math var *> can *> be *> pat <* iff)
    -- <|> ScanVerbInfinitive . toLexicalPhrase <$> (math var *> can *> pat <* iff)

inductive :: RE Token [ScannedLexicalItem]
inductive = do
    sym (BeginEnv "inductive")
    few notEndOfLexicalEnvToken
    m <- labelRE
    few anySym
    lexicalItem <- functionSymbolInductive
    few anySym
    sym (EndEnv "inductive")
    skipUntilNextLexicalEnv
    pure [ScanFunctionSymbol lexicalItem m]

structRE :: RE Token [ScannedLexicalItem]
structRE = do
    sym (BeginEnv "struct")
    few anySym
    m <- labelRE
    few anySym
    lexicalItem <- ScanStructNoun . toLexicalPhrase <$> (an *> structPat <* math var)
    few anySym
    lexicalItems <- structOps <|> pure []
    sym (EndEnv "struct")
    skipUntilNextLexicalEnv
    pure (lexicalItem m : lexicalItems)

structOps :: RE Token [ScannedLexicalItem]
structOps = do
    sym (BeginEnv "enumerate")
    lexicalItems <- many structOp
    sym (EndEnv "enumerate")
    few anySym
    pure lexicalItems

structOp :: RE Token ScannedLexicalItem
structOp = do
    sym (Command "item")
    op <- math command
    pure (ScanStructOp op)

nounRE :: RE Token LexicalPhrase
nounRE = toLexicalPhrase <$> (math var *> is *> an *> pat <* iff)

adjRE :: RE Token LexicalPhrase
adjRE = toLexicalPhrase <$> (math var *> is *> pat <* iff)

verbRE :: RE Token LexicalPhrase
verbRE = toLexicalPhrase <$> (math var *> pat <* iff)

funRE :: RE Token LexicalPhrase
funRE = toLexicalPhrase <$> (the *> pat <* (is <|> comma))

relationSymbolRE :: RE Token (RelationSymbol, Int)
relationSymbolRE = do
    beginMath
    var
    rel <- symbol
    k <- params
    var
    endMath
    iff
    pure (rel, k)
        where
        params :: RE Token Int
        params = do
            vars <- many (sym InvisibleBraceL *> var <* sym InvisibleBraceR)
            pure (length vars)

functionSymbolRE :: RE Token FunctionSymbol
functionSymbolRE = do
    sym (BeginEnv "math")
    toks <- few nonDefinitionKeyword
    sym (Symbol "=")
    pure case toks of
            -- TODO proper error messages with more info (location, etc.)
            [] -> error "Malformed function pattern: no pattern"
            [Variable _] -> error "Malformed function: bare variable. This will cause infinite left recursion in the grammar and cause the parser to hang!"
            [Variable _, ParenL, Variable _, ParenR] -> error "Malformed function: redefinition of function application. The notation _(_) is reserved for set-theoretic function application."
            _ -> fromToken <$> toks
    where
        fromToken = \case
            Variable _ -> Nothing -- Variables become slots.
            tok -> Just tok -- Everything else is part of the pattern.

functionSymbolInductive :: RE Token FunctionSymbol
functionSymbolInductive = do
    sym (BeginEnv "math")
    toks <- few nonDefinitionKeyword
    sym (Command "subseteq")
    pure (fromToken <$> toks)
    where
        fromToken = \case
            Variable _ -> Nothing -- Variables become slots.
            tok -> Just tok -- Everything else is part of the pattern.

prefixPredicate :: RE Token PrefixPredicate
prefixPredicate = math prfx <* iff
    where
        prfx = do
            r <- command
            args <- many (sym InvisibleBraceL *> var <* sym InvisibleBraceR)
            pure (PrefixPredicate r (length args))


command :: RE Token Text
command = msym \case
    Command cmd -> Just cmd
    _ -> Nothing

var :: RE Token Token
var = psym isVar


nonDefinitionKeyword :: RE Token Token
nonDefinitionKeyword = psym (`notElem` keywords)
    where
        keywords =
            [ Word "if"
            , Word "iff"
            , Symbol "="
            , Command "iff"
            , BeginEnv "math"
            , EndEnv "math"
            ]


pat :: RE Token [Token]
pat = many (psym isLexicalPhraseToken <|> math var)

structPat :: RE Token [Token]
structPat = many (psym isLexicalPhraseToken)

beginMath, endMath :: RE Token ()
beginMath = void (sym (BeginEnv "math"))
endMath = void (sym (EndEnv "math"))

math :: RE Token a -> RE Token a
math re = beginMath *> re <* endMath

-- | We allow /conditional perfection/: the first /@if@/ in a definition is interpreted as /@iff@/.
iff :: RE Token ()
iff = void (sym (Word "if")) -- Using @void@ is faster (only requires recognition).
    <|> void (sym (Word "iff"))
    <|> void (string [Word "if", Word "and", Word "only", Word "if"])
    <|> void (sym (Word "denote"))
    <|> void (sym (Word "stand") *> sym (Word "for"))
{-# INLINE iff #-}

an :: RE Token ()
an = void (sym (Word "a"))
    <|> void (sym (Word "an"))
{-# INLINE an #-}

is :: RE Token ()
is = void (sym (Word "is") <|> sym (Word "denotes"))
{-# INLINE is #-}

can :: RE Token ()
can = void (sym (Word "can"))
{-# INLINE can #-}

be :: RE Token ()
be = void (sym (Word "be"))
{-# INLINE be #-}

the :: RE Token ()
the = void (sym (Word "the"))
{-# INLINE the #-}

comma :: RE Token ()
comma = void (sym (Symbol ","))
{-# INLINE comma #-}


isVar :: Token -> Bool
isVar = \case
    Variable _ -> True
    _token -> False

isCommand :: Token -> Bool
isCommand = \case
    Command _ -> True
    _token -> False

isNotDefnToken :: Token -> Bool
isNotDefnToken = \case
    BeginEnv "definition" -> False
    EndEnv "definition" -> False
    _token -> True

isLexicalPhraseToken :: Token -> Bool
isLexicalPhraseToken = \case
    Word w -> w `Set.notMember` keywords
    --
    -- Simple commands (outside of math-mode) are allowed. This is useful
    -- for defining lexical phrases containing symbolic expressions such as
    -- `X is \Ttwo{}`, where `\Ttwo` is a macro that expands to `T_2`.
    -- We also allow these macros to take arguments, hence the need to
    -- allow grouping delimiters. They can also be used to escape the end
    -- of the command for correct spacing, as in the above example.
    --
    Command _cmd -> True
    InvisibleBraceL -> True
    InvisibleBraceR -> True
    --
    -- No other tokens may occur in lexical phrases. In particular, no `_dot`
    -- token may occur, limiting the lexical phrase to a single sentence.
    -- Commas occurring in variable lists should be placed
    -- within the math environment. Thus `$a,b$ are coprime iff`,
    -- not `$a$,`$b$` are coprime iff`.
    --
    _token -> False
    where
        keywords = Set.fromList ["a", "an", "is", "are", "if", "iff", "denote", "stand", "let"]


toLexicalPhrase :: [Token] -> LexicalPhrase
toLexicalPhrase toks = component <$> toks
    where
        component = \case
            Variable _ -> Nothing
            tok        -> Just tok


symbol :: RE Token Token
symbol = msym $ \tok -> case tok of
    Command _ -> Just tok
    Symbol _ -> Just tok
    _tok -> Nothing


-- | Basic paradigms for pluralizations of nominals.
guessNounPlural :: LexicalPhrase -> SgPl LexicalPhrase
guessNounPlural item = SgPl item (pluralize item)
    where
        pluralize :: LexicalPhrase -> LexicalPhrase
        pluralize = \case
            Just (Word w) : pat'@(Just w' : _) | isPreposition w' -> Just (Word (Text.snoc w 's')) : pat'
            tok : Just (Word w) : pat'@(Just w' : _) | isPreposition w' -> tok : Just (Word (Text.snoc w 's')) : pat'
            tok1 : tok2 : Just (Word w) : pat'@(Just w' : _) | isPreposition w' -> tok1 : tok2 : Just (Word (Text.snoc w 's')) : pat'
            [Just (Word w)] -> [Just (Word (Text.snoc w 's'))]
            [tok, Just (Word w)] -> [tok, Just (Word (Text.snoc w 's'))]
            [tok, tok', Just (Word w)] -> [tok, tok', Just (Word (Text.snoc w 's'))]
            pat' -> pat'

guessVerbPlural :: LexicalPhrase -> SgPl LexicalPhrase
guessVerbPlural item = SgPl item itemPl
    where
        itemPl = case item of
            Just (Word v) : rest -> case Text.unsnoc v of
                Just (v', 's') -> Just (Word v') : rest
                _ -> item
            _ -> item

isAdjR :: LexicalPhrase -> Bool
isAdjR item = containsPreposition item || containsSlot item
    where
        containsPreposition, containsSlot :: LexicalPhrase -> Bool
        containsPreposition = any isPreposition . catMaybes
        containsSlot = (Nothing `elem`)

isPreposition :: Token -> Bool
isPreposition w = HS.member w (HS.map Word prepositions)

-- | Right-biased set insertion, keeping the original set
-- when inserting already present elements. @insertR@ is unfortunately
-- a hidden function, even in @Data.Set.Internal@, so we approximate it
-- here. In theory one could avoid the indirection of first forming the singleton
-- set on the rhs.
insertR' :: Hashable a => a -> HashSet a -> HashSet a
insertR' x xs = xs `HS.union` HS.singleton x -- @union@ is left-biased.

insertMapR :: Ord k => k -> a -> Map k a -> Map k a
insertMapR k x xs = xs `Map.union` Map.singleton k x -- @union@ is left-biased.


insertR :: Hashable k => k -> a -> HashMap k a -> HashMap k a
insertR k x xs = xs `HM.union` HM.singleton k x -- @union@ is left-biased.

-- | Takes the scanned lexical phrases and inserts them in the correct
-- places in a lexicon.
extendLexicon :: [ScannedLexicalItem] -> Lexicon -> Lexicon
extendLexicon [] lexicon = lexicon
-- Note that we only consider 'sg' in the 'Ord' instance of SgPl, so that
-- known irregular plurals are preserved.
extendLexicon (scan : scans) lexicon@Lexicon{..} = case scan of
    ScanAdj item m -> if isAdjR item
        then extendLexicon scans lexicon{lexiconAdjRs = insertR item m lexiconAdjRs}
        else extendLexicon scans lexicon{lexiconAdjLs = insertR item m lexiconAdjLs}
    ScanFun item m ->
        extendLexicon scans lexicon{lexiconFuns = insertR (guessNounPlural item) m lexiconFuns}
    ScanVerb item m ->
        extendLexicon scans lexicon{lexiconVerbs = insertR (guessVerbPlural item) m lexiconVerbs}
    ScanNoun item m ->
        extendLexicon scans lexicon{lexiconNouns = insertR (guessNounPlural item) m lexiconNouns}
    ScanStructNoun item m ->
        extendLexicon scans lexicon{lexiconStructNouns = insertR (guessNounPlural item) m lexiconStructNouns}
    ScanRelationSymbol item m ->
        extendLexicon scans lexicon{lexiconRelationSymbols = insertR item m lexiconRelationSymbols}
    ScanFunctionSymbol item m ->
        if item `HM.member` lexiconMixfixMarkers
            then extendLexicon scans lexicon
            else extendLexicon scans lexicon
                { lexiconMixfixTable = Seq.adjust (HM.insert item NonAssoc) 9 lexiconMixfixTable
                , lexiconMixfixMarkers = HM.insert item m lexiconMixfixMarkers
                }
    ScanStructOp op ->
        extendLexicon scans lexicon{lexiconStructFun = insertR (StructSymbol op) (Marker op) lexiconStructFun}
    ScanPrefixPredicate tok m ->
        extendLexicon scans lexicon{lexiconPrefixPredicates = insertR tok m lexiconPrefixPredicates}
