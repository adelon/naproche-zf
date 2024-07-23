{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}

module Provers where

import Base
import Encoding
import Syntax.Lexicon (Lexicon)
import Syntax.Internal (Formula, Task(..), isIndirect)
import Tptp.UnsortedFirstOrder qualified as Tptp

import Control.Monad.Logger
import Data.Text qualified as Text
import Data.Time
import System.Process.Text (readProcessWithExitCode)
import Text.Builder

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
    | Error Text
    deriving (Show, Eq)

nominalDiffTimeToText :: NominalDiffTime -> Text
nominalDiffTimeToText delta = run (nominalDiffTimeToBuilder delta)

nominalDiffTimeToBuilder :: NominalDiffTime -> Builder
nominalDiffTimeToBuilder delta = case hours of
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


runProver :: (MonadIO io, MonadLogger io) => ProverInstance -> Lexicon -> Task -> io (Formula, ProverAnswer)
runProver prover@Prover{..} lexicon task = do
    startTime <- liftIO getCurrentTime
    let tptp = encodeTask lexicon task
    let tptp' = Tptp.toText tptp
    (_exitCode, answer, answerErr) <- liftIO (readProcessWithExitCode proverPath proverArgs tptp')
    endTime <- liftIO getCurrentTime
    let duration = timeDifferenceToText startTime endTime

    logInfoN
        let hypo = case tptp of
                Tptp.Task (head : _) -> Tptp.Task [head]
                _ -> Tptp.Task  []
        in  duration <> " " <> Tptp.toText hypo

    pure (taskConjecture task, recognizeAnswer prover task tptp' answer answerErr)


-- | Parse the answer of a prover based on the configured prefixes of responses.
recognizeAnswer :: ProverInstance -> Task -> Text -> Text -> Text -> ProverAnswer
recognizeAnswer Prover{..} task tptp answer answerErr =
    let
        matches prefixes   = any (\l -> any (`Text.isPrefixOf` l) prefixes) (Text.lines answer)
        saidYes            = matches proverSaysYes
        saidNo             = matches proverSaysNo
        doesNotKnow        = matches proverDoesNotKnow
        warned             = matches proverWarnsContradiction
    in if
        | saidYes || (warned && isIndirect task) -> Yes
        | saidNo -> No tptp
        | doesNotKnow -> Uncertain tptp
        | warned -> ContradictoryAxioms tptp
        | otherwise -> Error (answer <> answerErr)
