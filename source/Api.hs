{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Api
    ( constructTheoryGraph, TheoryGraph
    , tokenize, TokStream
    , scan
    , parse
    , simpleStream
    , builtins
    , ParseException(..)
    , gloss, GlossError(..)
    , generateTasks
    , encodeTasks
    , prepareDumpTasks
    , dumpTask
    , verify, verifyStreaming, ProverAnswer(..), VerificationResult(..)
    , exportMegalodon
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
    ) where


import Base
import Checking
import Checking.Cache
import Encoding
import Filter(filterTask)
import Meaning (meaning, GlossError(..))
import Megalodon qualified
import Provers
import Report.Location
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
import Data.IntSet qualified as IntSet
import Data.Set qualified as Set
import Data.Text.IO qualified as Text
import qualified Data.Text as Text
import GHC.Conc (getNumProcessors)
import System.FilePath.Posix
import Text.Earley (parser, fullParses, Parser, Report(..))
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
    currentDir <- getCurrentDirectory
    libraryDir <- (?? (currentDir </> "library")) <$> lookupEnv "NAPROCHE_LIB"

    existsCurrent     <- doesFileExist (currentDir </> path)
    existsUserLib     <- doesFileExist (libraryDir </> path)
    liftIO if
        | existsCurrent     -> Text.readFile (currentDir </> path)
        | existsUserLib     -> Text.readFile (libraryDir </> path)
        | otherwise         -> error $ unlines
            [ "Could not find file from relative path: " <> path
            , "Searched in:"
            , "  " <> currentDir </> path
            , "  " <> libraryDir </> path <> " (which you can override by setting the NAPROCHE_LIB environment variable)"
            ]


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
            let p :: [Located Token] -> ([Raw.Block], Report Text [Located Token])
                p = fullParses (parser (grammar lexicon))
            (, lexicon) <$> combineParseResults [p toks | toks <- chunks]

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
                "unconsumed " <> describeToken tok <> " at " <> prettyLocation (startPos ltok) <> "\n" <>
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
        Left err -> throwIO err
        Right blocks' -> pure (blocks', lexicon)


generateTasks :: (MonadIO io, MonadReader Options io) => FilePath -> io [Internal.Task]
generateTasks file = do
    dumpPremselTraining <- asks withDumpPremselTraining
    (blocks, lexicon) <- gloss file
    tasks <- liftIO (check dumpPremselTraining lexicon blocks)
    pure (contractionTask <$> tasks)

prepareCache :: MonadIO io => FilePath -> io FilePath
prepareCache file = do
    xdgCache <- getXdgDirectory XdgCache "zf"
    let cacheDir = xdgCache </> takeDirectory file
    let cache    = xdgCache </> file
    createDirectoryIfMissing True cacheDir
    -- Initialize with an empty cache when no cache exists.
    -- If we do not do this opening the cache file will fail.
    unlessM (doesFileExist cache)
        (putTaskCache cache [])
    pure cache

prepareDumpTasks :: (MonadIO io, MonadReader Options io) => FilePath -> io [(Int, Tptp.Task)]
prepareDumpTasks file = do
    tasks <- generateTasks file
    filterOption <- asks withFilter
    let filteredTasks = case filterOption of
            WithFilter -> filterTask <$> tasks
            WithoutFilter -> tasks
    let indexedTasks = zip [1..] filteredTasks
    cacheOption <- asks withCache
    indexedTasks' <- case cacheOption of
        WithoutCache -> pure indexedTasks
        WithCache -> do
            cache <- prepareCache file
            filterM (\(_, task) -> notInCache cache task) indexedTasks
    pure [(idx, encodeTask task) | (idx, task) <- indexedTasks']


encodeTasks :: (MonadIO io, MonadReader Options io) => FilePath -> io [Tptp.Task]
encodeTasks file = do
    tasks <- generateTasks file
    pure (encodeTask <$> tasks)

data VerificationResult
    = VerificationSuccess
    | VerificationFailure [(Internal.Formula, ProverAnswer)]
    deriving (Show)

isFailure :: (a, ProverAnswer) -> Bool
isFailure (_phi, Yes) = False
isFailure (_phi, _ans) = True

data VerificationWorkItem
    = VerifyTask Int Internal.Task
    | StopWorker

data VerificationProducerStopped = VerificationProducerStopped
    deriving (Show)

instance Exception VerificationProducerStopped

verifyStreaming :: (MonadUnliftIO io, MonadLogger io, MonadReader Options io) => ProverInstance -> FilePath -> io VerificationResult
verifyStreaming prover file = do
    dumpPremselTraining <- asks withDumpPremselTraining
    filterOption <- asks withFilter
    cacheOption <- asks withCache
    (blocks, lexicon) <- gloss file
    workerCount <- liftIO (max 1 . subtract 1 <$> getNumProcessors)
    workQueue <- liftIO (newTBQueueIO (fromIntegral workerCount))
    stopVar <- liftIO (newTVarIO False)
    nextTaskIndexVar <- liftIO (newTVarIO 0)
    firstFailureVar <- liftIO (newTVarIO Nothing)
    runInIO <- askRunInIO

    cacheState <- case cacheOption of
        WithoutCache -> pure Nothing
        WithCache -> do
            cacheFile <- prepareCache file
            hashedCache <- getTaskCache cacheFile
            hashedCacheVar <- liftIO (newTVarIO hashedCache)
            pure (Just (cacheFile, hashedCacheVar))

    let applyFilter :: Internal.Task -> Internal.Task
        applyFilter task = case filterOption of
            WithFilter -> filterTask task
            WithoutFilter -> task

        rememberTask :: Internal.Task -> IO ()
        rememberTask task = case cacheState of
            Nothing -> pure ()
            Just (_cacheFile, hashedCacheVar) ->
                atomically (modifyTVar' hashedCacheVar (IntSet.insert (hash task)))

        rememberFailure :: Int -> (Internal.Formula, ProverAnswer) -> IO ()
        rememberFailure idx failedAnswer = atomically do
            writeTVar stopVar True
            currentFailure <- readTVar firstFailureVar
            case currentFailure of
                Nothing ->
                    writeTVar firstFailureVar (Just (idx, failedAnswer))
                Just (oldIdx, _oldFailedAnswer) ->
                    when (idx < oldIdx) (writeTVar firstFailureVar (Just (idx, failedAnswer)))

        flushCache :: IO ()
        flushCache = case cacheState of
            Nothing -> pure ()
            Just (cacheFile, hashedCacheVar) -> do
                hashedCache <- atomically (readTVar hashedCacheVar)
                putTaskCacheHashes cacheFile hashedCache

        emitTask :: Internal.Task -> IO ()
        emitTask rawTask = do
            -- ASSUMPTION: There is exactly one emitter ('checkWith' callback), so
            -- queue insertion order is well-defined by this callback execution order.
            --
            -- If a failure has already been observed, stop emitting immediately.
            stopRequested <- atomically (readTVar stopVar)
            when stopRequested (throwIO VerificationProducerStopped)

            let task = applyFilter (contractionTask rawTask)
            shouldRun <- case cacheState of
                Nothing -> pure True
                Just (_cacheFile, hashedCacheVar) ->
                    atomically (IntSet.notMember (hash task) <$> readTVar hashedCacheVar)
            if shouldRun
                then do
                    -- The stop check and enqueue must be in one STM transaction.
                    -- This guarantees that no new task is enqueued after stopVar
                    -- has become True.
                    enqueueSucceeded <- atomically do
                        stopRequested' <- readTVar stopVar
                        if stopRequested'
                            then pure False
                            else do
                                nextTaskIndex <- readTVar nextTaskIndexVar
                                writeTVar nextTaskIndexVar (nextTaskIndex + 1)
                                writeTBQueue workQueue (VerifyTask nextTaskIndex task)
                                pure True
                    unless enqueueSucceeded (throwIO VerificationProducerStopped)
                else
                    skip

        worker :: IO ()
        worker = do
            item <- atomically (readTBQueue workQueue)
            case item of
                StopWorker ->
                    pure ()
                VerifyTask taskIndex task -> do
                    answer <- runInIO (runProver prover task)
                    if isFailure answer
                        then
                            rememberFailure taskIndex answer
                        else
                            rememberTask task
                    worker

        producer :: IO ()
        producer =
            checkWith dumpPremselTraining lexicon blocks emitTask
                `catch` \VerificationProducerStopped -> pure ()

        withAsyncs :: [IO a] -> ([Async a] -> IO b) -> IO b
        withAsyncs [] inner = inner []
        withAsyncs (action : actions) inner =
            withAsync action \a ->
                withAsyncs actions (\as -> inner (a : as))

    result <- liftIO $
        withAsyncs (replicate workerCount worker) \workerAsyncs -> do
            producerResult <- tryAny producer
            case producerResult of
                Left ex -> do
                    traverse_ cancel workerAsyncs
                    throwIO ex
                Right () -> do
                    -- Shutdown protocol:
                    -- 1) Producer has stopped.
                    -- 2) Enqueue one StopWorker sentinel per worker.
                    -- 3) Workers drain all earlier queued tasks, then terminate.
                    atomically (replicateM_ workerCount (writeTBQueue workQueue StopWorker))
                    traverse_ wait workerAsyncs
                    firstFailure <- atomically (readTVar firstFailureVar)
                    pure case firstFailure of
                        Just (_firstFailureIndex, failedAnswer) -> VerificationFailure [failedAnswer]
                        Nothing -> VerificationSuccess

    case result of
        VerificationSuccess -> liftIO flushCache
        VerificationFailure _ -> skip
    pure result

verify :: (MonadUnliftIO io, MonadLogger io, MonadReader Options io) => ProverInstance -> FilePath -> io VerificationResult
verify = verifyStreaming

dumpTask :: MonadIO io => FilePath -> Tptp.Task -> io ()
dumpTask file tptp = liftIO (Text.writeFile file (Tptp.toText tptp))

exportMegalodon :: (MonadUnliftIO io) => FilePath -> io Text
exportMegalodon file = do
    (blocks, _lexicon) <- gloss file
    pure (Megalodon.encodeBlocks blocks)
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
    }
