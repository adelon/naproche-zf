{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}

module CommandLine where

import Api
import Base
import Provers qualified
import Version qualified

import Control.Monad.Logger
import Control.Monad.Reader
import Data.Text.IO qualified as Text
import Data.Text.Lazy.IO qualified as LazyText
import Options.Applicative
import Text.Pretty.Simple (pShowNoColor)
import UnliftIO
import UnliftIO.Directory
import UnliftIO.Environment (lookupEnv)
import System.FilePath.Posix
import qualified Tptp.UnsortedFirstOrder as Syntax.Internal

runCommandLine :: IO ()
runCommandLine = do
    options@Options{withLogging = logging} <- execParser (withInfo parseOptions)
    case logging of
        WithoutLogging -> runNoLoggingT (runReaderT run options)
        WithLogging -> runStdoutLoggingT (runReaderT run options)
    where
        withInfo :: Parser a -> ParserInfo a
        withInfo p = info (helper <*> p) (fullDesc <> header "Naproche/ZF")


run :: (MonadUnliftIO io, MonadLogger io, MonadReader Options io) => io ()
run = do
    opts <- ask
    case withVersion opts of
        WithVersion -> liftIO (Text.putStrLn Version.info)
        WithoutVersion -> skip
    case withOmissions opts of
        WithoutOmissions -> liftIO (Text.putStrLn "--safe is not implemented yet.")
        WithOmissions -> skip
    case withDump opts of
        WithoutDump -> skip
        WithDump dir -> do
            let serials = [dir </> show n <.> "p" | n :: Int <- [1..]]
            tasks <- zip serials <$> encodeTasks (inputPath opts)
            createDirectoryIfMissing True dir
            forM_ tasks (uncurry dumpTask)
    case (withParseOnly opts, withMegalodon opts) of
        (WithParseOnly, _) -> do
            ast <- parse (inputPath opts)
            liftIO (LazyText.putStrLn (pShowNoColor ast))
        (_, WithMegalodon) -> do
            megalodon <- exportMegalodon (inputPath opts)
            let outputFile = "megalodon" </> replaceExtension (inputPath opts) "mg"
            createDirectoryIfMissing True (takeDirectory outputFile)
            liftIO (Text.writeFile outputFile megalodon)
        (WithoutParseOnly, WithoutMegalodon) -> do
            -- A custom E executable can be configured using environment variables.
            -- If the environment variable is undefined we fall back to the
            -- a globally installed E executable.
            vampirePathPath <- (?? "vampire") <$> lookupEnv "NAPROCHE_VAMPIRE"
            eproverPath <- (?? "eprover") <$> lookupEnv "NAPROCHE_EPROVER"
            let prover = case withProver opts of
                    WithVampire -> Provers.vampire vampirePathPath
                    WithEprover -> Provers.eprover eproverPath
                    WithIprover -> Provers.iprover
                    WithDefaultProver -> Provers.vampire vampirePathPath
            let proverInstance = prover Provers.Silent (withTimeLimit opts) (withMemoryLimit opts)
            result <- verify proverInstance (inputPath opts)
            case withFailList opts of
                WithoutFailList -> liftIO case result of
                    VerificationSuccess -> putStrLn "Verification successful."
                    VerificationFailure [] -> error "Empty verification fail"
                    VerificationFailure ((_, proverAnswer) : _) -> case proverAnswer of
                        Yes ->
                            skip
                        No tptp -> do
                            putStrLn "Verification failed: prover found countermodel"
                            Text.hPutStrLn stderr tptp
                        ContradictoryAxioms tptp -> do
                            putStrLn "Verification failed: contradictory axioms"
                            Text.hPutStrLn stderr tptp
                        Uncertain tptp -> do
                            putStrLn "Verification failed: out of resources"
                            Text.hPutStrLn stderr tptp
                        Error err tptp task -> do
                            putStr "Error at:"

                            Text.putStrLn task
                            Text.putStrLn err
                            Text.putStrLn tptp
                            
                WithFailList -> liftIO case result of
                    VerificationSuccess -> putStrLn "\ESC[32mVerification successful.\ESC[0m"
                    VerificationFailure [] -> error "Empty verification fail"
                    VerificationFailure fails -> do
                        putStrLn "\ESC[35mFollowing task couldn't be solved by the ATP: \ESC[0m"
                        traverse_ showFailedTask fails
                        Text.hPutStrLn stderr "Don't give up!"










parseOptions :: Parser Options
parseOptions = do
    inputPath <- strArgument (help "Source file" <> metavar "FILE")
    withCache <- withCacheParser
    withDump <- withDumpParser
    withFilter <- withFilterParser
    withLogging <- withLoggingParser
    withMemoryLimit <- withMemoryLimitParser
    withOmissions <- withOmissionsParser
    withParseOnly <- withParseOnlyParser
    withProver <- withProverParser
    withTimeLimit <- withTimeLimitParser
    withVersion <- withVersionParser
    withMegalodon <- withMegalodonParser
    withDumpPremselTraining <- withDumpPremselTrainingParser
    withFailList <- withFailListParser
    pure Options{..}

withTimeLimitParser :: Parser Provers.TimeLimit
withTimeLimitParser = Provers.Seconds <$> option auto (long "timelimit" <> short 't' <> value dflt <> help "Time limit for each proof task in seconds.")
    where
        Provers.Seconds dflt = Provers.defaultTimeLimit

withMemoryLimitParser :: Parser Provers.MemoryLimit
withMemoryLimitParser = Provers.Megabytes <$> option auto (long "memlimit" <> short 'm' <> value dflt <> help "Memory limit for each proof task in MB.")
    where
        Provers.Megabytes dflt = Provers.defaultMemoryLimit

withProverParser :: Parser WithProver
withProverParser = flag' WithEprover  (long "eprover" <> help "Use E as external prover.")
    <|> flag' WithVampire  (long "vampire" <> help "Use Vampire as external prover.")
    <|> flag' WithIprover (long "iprover" <> help "Use iProver as external prover.")
    <|> pure WithDefaultProver

withFilterParser :: Parser WithFilter
withFilterParser = flag' WithoutFilter (long "nofilter" <> help "Do not perform relevance filtering.")
    <|> flag' WithFilter (long "filter" <> help "Perform relevance filtering.")
    <|> pure WithoutFilter

withOmissionsParser :: Parser WithOmissions
withOmissionsParser = flag' WithOmissions (long "unsafe" <> help "Allow proof omissions (default).")
    <|> flag' WithoutOmissions (long "safe" <> help "Disallow proof omissions.")
    <|> pure WithOmissions -- Default to allowing omissions.

withParseOnlyParser :: Parser WithParseOnly
withParseOnlyParser = flag' WithParseOnly (long "parseonly" <> help "Only parse and show the resulting AST.")
    <|> pure WithoutParseOnly -- Default to allowing omissions.

withVersionParser :: Parser WithVersion
withVersionParser = flag' WithVersion (long "version" <> help "Show the current version.")
    <|> pure WithoutVersion -- Default to not showing the version.

withLoggingParser :: Parser WithLogging
withLoggingParser = flag' WithLogging (long "log" <> help "Enable logging.")
    <|> pure WithoutLogging -- Default to not showing the version.

withCacheParser :: Parser WithCache
withCacheParser = flag' WithoutCache (long "uncached" <> help "Do not use caching.")
    <|> flag' WithCache (long "cached" <> help "Use caching (default).")
    <|> pure WithCache -- Default to using the cache.

withDumpParser :: Parser WithDump
withDumpParser = WithDump <$> strOption (long "dump" <> metavar "DUMPDIR" <> help "Dump all proof tasks in a separate directory.")
    <|> pure WithoutDump -- Default to using the cache.

withDumpPremselTrainingParser :: Parser WithDumpPremselTraining
withDumpPremselTrainingParser = flag' WithDumpPremselTraining (long "premseldump" <> help "Dump training data for premise selection.")
    <|> pure WithoutDumpPremselTraining -- Default to using the cache.

withMegalodonParser :: Parser WithMegalodon
withMegalodonParser = flag' WithMegalodon (long "megalodon" <> help "Export to Megalodon.")
    <|> pure WithoutMegalodon -- Default to using the cache.

withFailListParser :: Parser WithFailList
withFailListParser = flag' WithFailList (long "list_fails" <> help "Will list all unproven task with possible reason of failure.")
    <|> pure WithoutFailList -- Default to using the cache.