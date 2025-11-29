{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}

module Api
    ( constructTheoryGraph, TheoryGraph
    , tokenize, TokStream
    , scan
    , parse
    , simpleStream
    , builtins
    , ParseException(..)
    , gloss, GlossError(..), GlossException(..)
    , generateTasks
    , encodeTasks
    , dumpTask
    , verify, ProverAnswer(..), VerificationResult(..)
    , exportMegalodon
    , showFailedTask
    , WithCache(..)
    , WithFilter(..)
    , WithOmissions(..)
    , WithProver(..)
    , WithVersion(..)
    , WithLogging(..)
    , WithDump(..)
    , WithMegalodon(..)
    , pattern WithoutDump
    , WithParseOnly(..)
    , Options(..)
    , WithDumpPremselTraining(..)
    , WithFailList(..)
    ) where


import Base
import Checking
import Checking.Cache
import Encoding
import Filter(filterTask)
import Meaning (meaning, GlossError(..))
import Megalodon qualified
import Provers
import Syntax.Abstract qualified as Raw
import Syntax.Adapt (adaptChunks, scanChunk, ScannedLexicalItem)
import Syntax.Concrete
import Syntax.Internal qualified as Internal
import Syntax.Lexicon (Lexicon, builtins)
import Syntax.Token
import TheoryGraph (TheoryGraph, Precedes(..))
import TheoryGraph qualified
import Tptp.UnsortedFirstOrder qualified as Tptp

import Control.Monad.Logger
import Data.List (intercalate)
import Control.Monad.Reader
import Data.Set qualified as Set
import Data.List qualified as List
import Data.Text.IO qualified as Text
import qualified Data.Text as Text
import System.FilePath.Posix
import Text.Earley (parser, fullParses, Report(..))
import Text.Megaparsec hiding (parse, Token)
import UnliftIO
import UnliftIO.Directory
import UnliftIO.Environment

-- | Follow all @\\import@ statements recursively and build a theory graph from them.
-- The @\\import@ statements should be on their own separate line and precede all
-- top-level environments. This process is entirely decoupled from tokenizing and
-- parsing processes.
constructTheoryGraph :: forall io. MonadIO io => FilePath -> io TheoryGraph
constructTheoryGraph root = fmap snd (go mempty (TheoryGraph.singleton root) root)
    where
    go :: Set FilePath -> TheoryGraph -> FilePath -> io (Set FilePath, TheoryGraph)
    go visited graph file =
        if file `Set.member` visited then pure (visited, graph)
        else do
            raw <- findAndReadFile file
            let files = gatherImports raw
            let visited' = Set.insert file visited
            let precedes = [ancestor `Precedes` file | ancestor <- files]
            let graph' = TheoryGraph.fromList precedes <> graph
            results <- go visited' graph' `traverse` files
            let (visited'', graph'') = unzip results
            pure (visited' <> Set.unions visited'', graph' <> TheoryGraph.unions graph'')


-- | Given a filename for a theory, look for it in a set of predetermined places:
-- the current directory, the library directory, and the Naproche root directory.
findAndReadFile :: MonadIO io => FilePath -> io Text
findAndReadFile path = do
    homeDir     <- getHomeDirectory
    currentDir  <- getCurrentDirectory
    userLib     <- (?? (homeDir </> "formalizations"))   <$> lookupEnv "NAPROCHE_LIB"
    srcLib      <- (?? (homeDir </> "code/naproche-zf/library"))  <$> lookupEnv "NAPROCHE_SCR_LIB"

    existsCurrent     <- doesFileExist (currentDir </> path)
    existsUserLib     <- doesFileExist (userLib </> path)
    existsScrLib      <- doesFileExist (srcLib </> path)
    liftIO if
        | existsCurrent     -> Text.readFile (currentDir </> path)
        | existsUserLib     -> Text.readFile (userLib </> path)
        | existsScrLib      -> Text.readFile (srcLib </> path)
        | otherwise         -> error ("Could not find file: " <> path)


-- | Throws a 'ParseException' when tokenizing fails.
tokenize :: MonadIO io => FilePath -> io TokStream
tokenize file = do
    raw <- findAndReadFile file
    case runLexer file raw of
        Left tokenError -> throwIO (TokenError (errorBundlePretty tokenError))
        Right (_imports, chunks) -> pure (TokStream raw chunks)

-- | Scan the given file for lexical items. The actual parsing process
-- uses 'adaptChunks' instead.
scan :: MonadIO io => FilePath -> io [ScannedLexicalItem]
scan input = do
    tokenStream <- tokenize input
    pure (concatMap scanChunk (unTokStream tokenStream))


-- | Parse a file. Throws a 'ParseException' when tokenizing, scanning, or
-- parsing fails.
parse :: MonadIO io => FilePath -> io ([Raw.Block], Lexicon)
parse file = do
    -- We need to consider the entire theory graph here already
    -- since we can use vocabulary of imported theories.
    theoryGraph <- constructTheoryGraph file
    case TheoryGraph.topSortSeq theoryGraph of
        -- LATER replace with a more helpful error message, like actually showing the cycle properly
        Left cyc -> error ("could not linearize theory graph (likely due to circular dependencies):\n" <> show cyc)
        Right theoryChain -> do
            tokenStreams <- traverse tokenize theoryChain
            let tokenStream = mconcat (toList tokenStreams)
            let chunks = unTokStream tokenStream
            let lexicon = adaptChunks chunks builtins
            (, lexicon) <$> combineParseResults [fullParses (parser (grammar lexicon)) toks | toks <- chunks]

combineParseResults :: MonadIO io => [([Raw.Block], Report Text [Located Token])] -> io [Raw.Block]
combineParseResults [] = pure []
combineParseResults (result : results) = case result of
    (_, Report _ es (tok:toks)) -> throwIO (UnconsumedTokens es (tok :| toks))
    ([], _) -> throwIO EmptyParse
    (ambi@(_:_:_), _) -> case nubOrd ambi of
        [block] -> do
            blocks <- combineParseResults results
            pure (trace ("technically ambiguous parse:\n" <> show block) (block : blocks))
        ambi' -> throwIO (AmbigousParse ambi')
    ([block], _) -> do
        blocks <- combineParseResults results
        pure (block : blocks)


simpleStream :: TokStream -> [[Token]]
simpleStream TokStream{unTokStream=chunks} = [unLocated <$> ch | ch <- chunks]


data ParseException
    = UnconsumedTokens [Text] (NonEmpty (Located Token)) -- ^ Expectations and unconsumed tokens.
    | AmbigousParse [Raw.Block]
    | EmptyParse
    | TokenError String

instance Show ParseException where
    show = \case
        UnconsumedTokens es (ltok :| ltoks) ->
            let tok = unLocated ltok
                toks = unLocated <$> ltoks
            in
                "unconsumed " <> describeToken tok <> " at " <> sourcePosPretty (startPos ltok) <> "\n" <>
                "  " <> unwords (tokToString <$> (tok : take 4 toks)) <> "\n" <>
                "  " <> replicate (length (tokToString tok)) '^' <> "\n" <>
                case es of
                    [] -> "while expecting nothing"
                    _ -> "while expecting one of the following:\n" <> intercalate ", " (Text.unpack <$> nubOrd es)
        AmbigousParse blocks ->
            "ambiguous parse: " <> show blocks
        EmptyParse ->
            "empty parse"
        TokenError err ->
            err -- Re-use pretty printing from Megaparsec.

instance Exception ParseException where


describeToken :: Token -> String
describeToken = \case
    Word _ -> "word"
    Variable _ -> "variable"
    Symbol _ -> "symbol"
    Integer _ -> "integer"
    Command _ -> "command"
    BeginEnv _ -> "begin of environment"
    EndEnv _ -> "end of environment"
    _ -> "delimiter"

-- | gloss generates internal represantation of the LaTeX files.
-- First the file will be parsed and therefore checkt for grammer.
-- 'meaning' then transfer the raw parsed grammer to the internal semantics.
gloss :: MonadIO io => FilePath -> io ([Internal.Block], Lexicon)
gloss file = do
    (blocks, lexicon) <- parse file
    case meaning blocks of
        Left err -> throwIO (GlossException err)
        Right blocks' -> pure (blocks', lexicon)


newtype GlossException
    = GlossException GlossError
    deriving (Show, Eq)

instance Exception GlossException



generateTasks :: (MonadIO io, MonadReader Options io) => FilePath -> io ([Internal.Task], Lexicon)
generateTasks file = do
    dumpPremselTraining <- asks withDumpPremselTraining
    (blocks, lexicon) <- gloss file
    tasks <- liftIO (check dumpPremselTraining lexicon blocks)
    pure (Internal.contractionTask <$> tasks, lexicon)


encodeTasks :: (MonadIO io, MonadReader Options io) => FilePath -> io [Tptp.Task]
encodeTasks file = do
    (tasks, lexicon) <- generateTasks file
    pure (encodeTask lexicon <$> tasks)

data VerificationResult
    = VerificationSuccess
    | VerificationFailure [(Internal.Formula, ProverAnswer)]
    deriving (Show)

resultFromAnswers :: [(Internal.Formula, ProverAnswer)] -> VerificationResult
resultFromAnswers answers =
    case List.filter isFailure answers of
        [] -> VerificationSuccess
        failures -> VerificationFailure failures

isFailure :: (a, ProverAnswer) -> Bool
isFailure (_phi, Yes) = False
isFailure (_phi, _ans) = True

verify :: (MonadUnliftIO io, MonadLogger io, MonadReader Options io) => ProverInstance -> FilePath -> io VerificationResult
verify prover file = do
    (tasks, lexicon) <- generateTasks file
    filterOption <- asks withFilter
    let filteredTasks = case filterOption of
            WithFilter -> filterTask <$> tasks
            WithoutFilter -> tasks
    cacheOption <- asks withCache
    answers <- case cacheOption of
        WithoutCache ->
            pooledForConcurrently filteredTasks (runProver prover lexicon)
        WithCache -> do
            xdgCache <- getXdgDirectory XdgCache "zf"
            let cacheDir = xdgCache </> takeDirectory file
            let cache    = xdgCache </> file
            createDirectoryIfMissing True cacheDir
            -- Initialize with an empty cache when no cache exists.
            -- If we do not do this opening the cache file will fail.
            unlessM (doesFileExist cache)
                (putTaskCache cache [])

            filteredTasks' <- filterM (notInCache cache) filteredTasks
            answers' <- pooledForConcurrently filteredTasks' (runProver prover lexicon)

            -- MAYBE: use Seq.breakl
            let firstFailure = find (\(_, answer) -> isFailure answer) (List.zip filteredTasks' answers')
            let successfulPrefix = List.takeWhile (\task -> Just task /= (fst <$> firstFailure)) filteredTasks
            putTaskCache cache successfulPrefix
            pure answers'
    pure (resultFromAnswers answers)

dumpTask :: MonadIO io => FilePath -> Tptp.Task -> io ()
dumpTask file tptp = liftIO (Text.writeFile file (Tptp.toText tptp))

exportMegalodon :: (MonadUnliftIO io) => FilePath -> io Text
exportMegalodon file = do
    (blocks, lexicon) <- gloss file
    pure (Megalodon.encodeBlocks lexicon blocks)



-- | This could be expandend with the dump case, with dump off just this and if dump is on it could show the number off the task. For quick use
showFailedTask :: (a, ProverAnswer) -> IO()
showFailedTask (_, Yes ) = Text.putStrLn ""
showFailedTask (_, No tptp) = Text.putStrLn (Text.pack ("\ESC[31mProver found countermodel: \ESC[0m" ++ Text.unpack(Text.unlines (take 1 (Text.splitOn "." tptp)))))
showFailedTask (_, ContradictoryAxioms tptp) = Text.putStrLn (Text.pack ("\ESC[31mContradictory axioms: \ESC[0m" ++ Text.unpack(Text.unlines (take 1 (Text.splitOn "." tptp)))))
showFailedTask (_, Uncertain tptp) = Text.putStrLn (Text.pack ("\ESC[31mOut of resources: \ESC[0m" ++ Text.unpack(Text.unlines (take 1 (Text.splitOn "." tptp)))))
showFailedTask (_, Error _ tptp _) = Text.putStrLn (Text.pack ("\ESC[31mError at: \ESC[0m" ++ Text.unpack(Text.unlines (take 1 (Text.splitOn "." tptp)))))
--showFailedTask (_, _) = Text.putStrLn "Error!"


-- | Should we use caching?
data WithCache = WithoutCache | WithCache deriving (Show, Eq)

data WithFilter = WithoutFilter | WithFilter deriving (Show, Eq)

-- | Are proof omissions allowed?
data WithOmissions = WithoutOmissions | WithOmissions deriving (Show, Eq)

-- | Which external prover should be used?
data WithProver = WithDefaultProver | WithEprover | WithVampire | WithIprover deriving (Show, Eq)

-- | Should we show the version of the software?
data WithVersion = WithoutVersion | WithVersion deriving (Show, Eq)

data WithLogging = WithoutLogging | WithLogging deriving (Show, Eq)

-- | Should we dump all proof tasks? Where?
newtype WithDump = WithDump FilePath deriving (Show, Eq)

-- | Should we export to Megalodon?
data WithMegalodon = WithMegalodon | WithoutMegalodon deriving (Show, Eq)

pattern WithoutDump :: WithDump
pattern WithoutDump = WithDump ""

data WithParseOnly = WithoutParseOnly | WithParseOnly deriving (Show, Eq)

data WithFailList = WithoutFailList | WithFailList deriving (Show, Eq)


data Options = Options
    { inputPath :: FilePath
    , withCache :: WithCache
    , withDump :: WithDump
    , withFilter :: WithFilter
    , withLogging :: WithLogging
    , withMemoryLimit :: Provers.MemoryLimit
    , withOmissions :: WithOmissions
    , withParseOnly :: WithParseOnly
    , withProver :: WithProver
    , withTimeLimit :: Provers.TimeLimit
    , withVersion :: WithVersion
    , withMegalodon :: WithMegalodon
    , withDumpPremselTraining :: WithDumpPremselTraining
    , withFailList :: WithFailList
    }
