module Syntax.Chunk where

import Base
import Syntax.Token

import Data.List qualified as List


-- LATER This is just a naïve implementation of token chunks.
-- It and  the current tokenizer should probably be replaced by
-- a more efficient implementation that does chunking
-- directly while tokenizing.

chunkify :: [Located Token] -> [[Located Token]]
chunkify [] = []
chunkify (tok : toks) = case unLocated tok of
    BeginEnv env | isTopLevelEnv env ->
        let (axiomToks, otherToks) = envBlock env toks
        in  (tok : axiomToks) : chunkify otherToks
    --
    -- Skip all tokens outside of toplevel environments.
    _ -> chunkify toks

isTopLevelEnv :: Text -> Bool
isTopLevelEnv env = env `elem`
    [ "abbreviation"
    , "axiom"
    , "claim"
    , "corollary"
    , "datatype"
    , "definition"
    , "inductive"
    , "lemma"
    , "proof"
    , "proposition"
    , "signature"
    , "struct"
    , "theorem"
    ]

envBlock :: Text -> [Located Token] -> ([Located Token], [Located Token])
envBlock env toks =
    let (pre, post) = List.span (\tok -> unLocated tok /= EndEnv env) toks
    in case post of
        [] -> (pre, post)
        endEnv : post' -> (pre ++ [endEnv], post')
