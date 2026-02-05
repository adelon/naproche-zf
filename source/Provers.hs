{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}

module Provers where

import Base
import Encoding
import Syntax.Internal (Formula, Task(..), isIndirect)

import Control.Exception (evaluate)
import Control.Monad.Logger
import Data.Text qualified as Text
import Data.Text.IO qualified as TextIO
import Data.Time
import System.Exit (ExitCode)
import System.IO (hClose)
import System.Process (CreateProcess(..), StdStream(CreatePipe), createProcess, proc, waitForProcess)
import TextBuilder

type Prover = Verbosity -> TimeLimit -> MemoryLimit -> ProverInstance

-- | Prover responses are stored as a list of prefixes.
data ProverInstance = Prover
    { proverName :: String
    , proverPath :: FilePath
    , proverArgs :: [String]
    , proverSaysYes :: [Text]
    , proverSaysNo :: [Text]
    , proverDoesNotKnow :: [Text]
    , proverWarnsContradiction :: [Text]
    } deriving (Show, Eq)


data Verbosity = Silent | Verbose deriving (Show, Eq)
newtype TimeLimit = Seconds Word64 deriving (Show, Eq, Num)
newtype MemoryLimit = Megabytes Word64 deriving (Show, Eq)

toSeconds :: TimeLimit -> String
toSeconds (Seconds secs) = show secs

toMegabytes :: MemoryLimit -> String
toMegabytes (Megabytes mbs) = show mbs

defaultTimeLimit :: TimeLimit
defaultTimeLimit = Seconds 10

defaultMemoryLimit :: MemoryLimit
defaultMemoryLimit = Megabytes 5000


eproverDev :: ProverInstance
eproverDev = eprover "eprover" Silent defaultTimeLimit defaultMemoryLimit

eprover :: FilePath -> Prover
eprover path verbosity timeLimit memoryLimit = Prover
    { proverName = "eprover"
    , proverPath = path
    , proverArgs =
        [ "--tptp3-format"
        , "--auto"
        , case verbosity of
            Silent  -> "--silent"
            Verbose -> "--verbose"
        , "--soft-cpu-limit=" <> toSeconds timeLimit
        , "--cpu-limit=" <> toSeconds (timeLimit + 5)
        , "--memory-limit=" <> toMegabytes memoryLimit
        ]
    , proverSaysYes = ["# SZS status Theorem"]
    , proverSaysNo = ["# SZS status CounterSatisfiable"]
    , proverDoesNotKnow = ["# SZS status ResourceOut", "# SZS status GaveUp"]
    , proverWarnsContradiction = ["# SZS status ContradictoryAxioms"]
    }


vampire :: FilePath -> Prover
vampire path _verbosity timeLimit memoryLimit = Prover
    { proverName = "vampire"
    , proverPath = path
    , proverArgs =
        [ "--mode", "casc"
        , "--time_limit", toSeconds timeLimit
        , "--memory_limit", toMegabytes memoryLimit
        ]
    , proverSaysYes = ["% SZS status Theorem"]
    , proverSaysNo = ["% SZS status CounterSatisfiable"]
    , proverDoesNotKnow = ["% SZS status Timeout"]
    , proverWarnsContradiction = ["% SZS status ContradictoryAxioms"]
    }

-- WIP: setting up a clausifier
iprover :: Prover
iprover _verbosity timeLimit _memoryLimit = Prover
    { proverName = "iProver"
    , proverPath = "iproveropt"
    , proverArgs =
        [ "--time_out_real " <> toSeconds timeLimit
        ]
    , proverSaysYes = ["% SZS status Theorem"]
    , proverSaysNo = ["% SZS status CounterSatisfiable"]
    , proverDoesNotKnow = ["% SZS status Unknown"]
    , proverWarnsContradiction = []
    }

-- | 'No', 'Uncertain', and 'ContradictoryAxioms' carry the 'Text'-encoded
-- TPTP problem that failed with them for debugging purposes. 'Error' simply
-- contains the error message of the prover verbatim.
data ProverAnswer
    = Yes
    | No Text
    | ContradictoryAxioms Text
    | Uncertain Text
    | Error Text Text Text
    deriving (Show, Eq)

nominalDiffTimeToText :: NominalDiffTime -> Text
nominalDiffTimeToText delta = TextBuilder.toText (nominalDiffTimeToTextBuilder delta)

nominalDiffTimeToTextBuilder :: NominalDiffTime -> TextBuilder
nominalDiffTimeToTextBuilder delta = case hours of
        0 -> padded minutes <> ":" <> padded restSeconds <> "." <> padded restCentis
        _ -> padded hours   <> ":" <> padded restMinutes <> ":" <> padded restSeconds
    where
        padded n = if n < 10 then char '0' <> decimal n else decimal n
        centiseconds = truncate (100 * nominalDiffTimeToSeconds delta) :: Int
        (seconds, restCentis) = divMod centiseconds 100
        (minutes, restSeconds) = divMod seconds 60
        (hours, restMinutes)   = divMod minutes 60

timeDifferenceToText :: UTCTime -> UTCTime -> Text
timeDifferenceToText startTime endTime = nominalDiffTimeToText (diffUTCTime endTime startTime)


runProver :: (MonadIO io, MonadLogger io) => ProverInstance -> Task -> io (Formula, ProverAnswer)
runProver prover@Prover{..} task = do
    startTime <- liftIO getCurrentTime
    (exitCode, answer, answerErr) <- liftIO (runProverProcess proverPath proverArgs task)
    endTime <- liftIO getCurrentTime
    let duration = timeDifferenceToText startTime endTime

    logInfoN
        let conjLine = encodeConjectureLine (taskConjectureLabel task) (taskLocation task) (taskDirectness task) (taskConjecture task)
        in  duration <> " " <> toText conjLine

    pure (taskConjecture task, recognizeAnswer prover task answer answerErr)

runProverProcess :: FilePath -> [String] -> Task -> IO (ExitCode, Text, Text)
runProverProcess path args task = do
    (Just hin, Just hout, Just herr, ph) <-
        createProcess (proc path args){std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
    writeTask hin task
    hClose hin
    out <- TextIO.hGetContents hout
    err <- TextIO.hGetContents herr
    _ <- evaluate (Text.length out + Text.length err)
    exitCode <- waitForProcess ph
    pure (exitCode, out, err)


-- | Parse the answer of a prover based on the configured prefixes of responses.
recognizeAnswer :: ProverInstance -> Task -> Text -> Text -> ProverAnswer
recognizeAnswer Prover{..} task answer answerErr =
    let
        matches prefixes   = any (\l -> any (`Text.isPrefixOf` l) prefixes) (Text.lines answer)
        saidYes            = matches proverSaysYes
        saidNo             = matches proverSaysNo
        doesNotKnow        = matches proverDoesNotKnow
        warned             = matches proverWarnsContradiction
    in if
        | saidYes || (warned && isIndirect task) -> Yes
        | saidNo -> No (encodeTaskText task)
        | doesNotKnow -> Uncertain (encodeTaskText task)
        | warned -> ContradictoryAxioms (encodeTaskText task)
        | otherwise -> Error (answer <> answerErr) (encodeTaskText task) (Text.pack(show (taskConjectureLabel task)))
