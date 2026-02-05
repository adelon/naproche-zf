{-# LANGUAGE NoImplicitPrelude #-}

-- | The 'Lexicon' describes the part of the grammar that extensible/dynamic.
--
-- The items of the 'Lexicon' are organized by their meaning and their
-- syntactic behaviour. They are typically represented as some kind of
-- pattern data which is then used to generate various production rules
-- for the concrete grammar. This representation makes inspection and
-- extension easier.
--

module Syntax.Lexicon
    ( module Syntax.Lexicon
    , pattern ConsSymbol
    , pattern PairSymbol
    , pattern CarrierSymbol
    , pattern ApplySymbol
    , pattern DomSymbol
    ) where


import Base
import Syntax.Abstract

import Data.List qualified as List
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Syntax.Mixfix (Holey)


data Lexicon = Lexicon
    { lexiconMixfixTable        :: Seq (Map Pattern MixfixItem)
    , lexiconConnectives        :: [[(Holey Token, Associativity)]]
    , lexiconPrefixPredicates   :: [(PrefixPredicate, Marker)]
    , lexiconStructFun          :: [StructSymbol]
    , lexiconRelationSymbols    :: [RelationSymbol]
    , lexiconVerbs              :: [LexicalItemSgPl]
    , lexiconAdjLs              :: [LexicalItem]
    , lexiconAdjRs              :: [LexicalItem]
    , lexiconNouns              :: [LexicalItemSgPl]
    , lexiconStructNouns        :: [LexicalItemSgPl]
    , lexiconFuns               :: [LexicalItemSgPl]
    } deriving (Show, Eq)

-- Projection returning the union of both left and right attributes.
--
lexiconAdjs :: Lexicon -> [LexicalItem]
lexiconAdjs lexicon = lexiconAdjLs lexicon <> lexiconAdjRs lexicon


builtins :: Lexicon
builtins = Lexicon
    { lexiconMixfixTable        = builtinMixfixTable
    , lexiconPrefixPredicates   = builtinPrefixPredicates
    , lexiconStructFun          = builtinStructOps
    , lexiconConnectives        = builtinConnectives
    , lexiconRelationSymbols    = builtinRelationSymbols
    , lexiconAdjLs              = []
    , lexiconAdjRs              = builtinAdjRs
    , lexiconVerbs              = builtinVerbs
    , lexiconNouns              = builtinNouns
    , lexiconStructNouns        = builtinStructNouns
    , lexiconFuns               = []
    }

builtinMixfixTable :: Seq (Map Pattern MixfixItem)
builtinMixfixTable = Seq.fromList $ Map.fromList . fmap toEntry <$> builtinMixfixLevels
    where
        toEntry item@(MixfixItem pat _ _) = (pat, item)

-- INVARIANT: 10 precedence levels for now.
builtinMixfixLevels :: [[MixfixItem]]
builtinMixfixLevels =
    [ []
    , [binOp (Symbol "+") LeftAssoc "add", binOp (Command "union") LeftAssoc "union", binOp (Symbol "-") LeftAssoc "minus", binOp (Command "rminus") LeftAssoc "rminus", binOp (Command "monus") LeftAssoc "monus"]
    , [binOp (Command "relcomp") LeftAssoc "relcomp"]
    , [binOp (Command "circ") LeftAssoc "circ"]
    , [binOp (Command "mul") LeftAssoc "mul", binOp (Command "inter") LeftAssoc "inter", binOp (Command "rmul") LeftAssoc "rmul"]
    , [binOp (Command "setminus") LeftAssoc "setminus"]
    , [binOp (Command "times") RightAssoc "times"]
    , []
    , prefixOps
    , builtinIdentifiers
    ]
    where
        builtinIdentifiers :: [MixfixItem]
        builtinIdentifiers = identifier <$>
            [ "emptyset"
            , "naturals"
            , "naturalsPlus"
            , "integers"
            , "rationals"
            , "reals"
            , "unit"
            , "zero"
            ]


prefixOps :: [MixfixItem]
prefixOps =
    [ mkMixfixItem [Just (Command "rfrac"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "rfrac" NonAssoc
    , mkMixfixItem [Just (Command "exp"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "exp" NonAssoc
    , mkMixfixItem [Just (Command "unions"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "unions" NonAssoc
    , mkMixfixItem [Just (Command "cumul"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "cumul" NonAssoc
    , mkMixfixItem [Just (Command "fst"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "fst" NonAssoc
    , mkMixfixItem [Just (Command "snd"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "snd" NonAssoc
    , mkMixfixItem [Just (Command "pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "pow" NonAssoc
    , mkMixfixItem [Just (Command "neg"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "neg" NonAssoc
    , mkMixfixItem [Just (Command "inv"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "inv" NonAssoc
    , mkMixfixItem [Just (Command "abs"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "abs" NonAssoc
    , ConsSymbol
    , PairSymbol
    -- NOTE Is now defined and hence no longer necessary , ApplySymbol
    ]


builtinStructOps :: [StructSymbol]
builtinStructOps =
    [ CarrierSymbol
    ]

identifier :: Text -> MixfixItem
identifier cmd = mkMixfixItem [Just (Command cmd)] (Marker cmd) NonAssoc


builtinRelationSymbols :: [RelationSymbol]
builtinRelationSymbols =
    [ RelationSymbol (Symbol "=") "eq"
    , RelationSymbol (Command "rless") "rless"
    , RelationSymbol (Command "neq") "neq"
    , ElementSymbol
    , NotElementSymbol -- Alternative to @\not\in@.
    ]

builtinPrefixPredicates :: [(PrefixPredicate, Marker)]
builtinPrefixPredicates =
    [ (PrefixPredicate "Cong" 4, "cong")
    , (PrefixPredicate "Betw" 3, "betw")
    ]


builtinConnectives :: [[(Holey Token, Associativity)]]
builtinConnectives =
    [ [binOp' (Command "iff") NonAssoc]
    , [binOp' (Command "implies") RightAssoc]
    , [binOp' (Command "lor") LeftAssoc]
    , [binOp' (Command "land") LeftAssoc]
    , [([Just (Command "lnot"), Nothing], NonAssoc)]
    ]


binOp :: Token -> Associativity -> Marker -> MixfixItem
binOp tok assoc m = mkMixfixItem [Nothing, Just tok, Nothing] m assoc

binOp' :: Token -> Associativity -> (Holey Token, Associativity)
binOp' tok assoc = ([Nothing, Just tok, Nothing], assoc)

builtinAdjRs :: [LexicalItem]
builtinAdjRs =
    [ mkLexicalItem (unsafeReadPhrase "equal to ?") "eq"
    ]

builtinVerbs :: [LexicalItemSgPl]
builtinVerbs =
    [ mkLexicalItemSgPl (unsafeReadPhraseSgPl "equal[s/] ?") "eq"
    ]


-- Some of these do/should correspond to mathlib structures,
-- e.g.: lattice, complete lattice, ring, etc.
--
builtinNouns :: [LexicalItemSgPl]
builtinNouns = mkNoun <$>
    -- Nullary
    [ ("set[/s]", "set")
    , ("point[/s]", "point")
    , ("element[/s] of ?", "elem")
    ]
    where
        mkNoun (spec, m) = mkLexicalItemSgPl (unsafeReadPhraseSgPl spec) (Marker m)

_Onesorted :: LexicalItemSgPl
_Onesorted = mkLexicalItemSgPl (unsafeReadPhraseSgPl "onesorted structure[/s]") "onesorted_structure"

builtinStructNouns :: [LexicalItemSgPl]
builtinStructNouns = [_Onesorted]


-- | Naïve splitting of lexical phrases to insert a variable slot for names in noun phrases,
-- as in /@there exists a linear form $h$ on $E$@/, where the underlying pattern is
-- /@linear form on ?@/. In this case we would get:
--
-- > splitOnVariableSlot (sg (unsafeReadPhraseSgPl "linear form[/s] on ?"))
-- > ==
-- > (unsafeReadPhrase "linear form", unsafeReadPhrase "on ?")
--
splitOnVariableSlot :: LexicalPhrase -> (LexicalPhrase, LexicalPhrase)
splitOnVariableSlot pat = case prepositionIndices <> nonhyphenatedSlotIndices of
    [] -> (pat, []) -- Place variable slot at the end.
    is -> List.splitAt (minimum is) pat
    where
        prepositionIndices, slotIndices, nonhyphenatedSlotIndices :: [Int] -- Ascending.
        prepositionIndices = List.findIndices isPreposition pat
        slotIndices = List.findIndices isNothing pat
        nonhyphenatedSlotIndices = [i | i <- slotIndices, noHyphen (nth (i + 1) pat)]

        isPreposition :: Maybe Token -> Bool
        isPreposition = \case
            Just (Word w) -> w `Set.member` prepositions
            _ -> False

        noHyphen :: Maybe (Maybe Token) -> Bool
        noHyphen = \case
            Just (Just (Word w)) -> Text.head w /= '-'
            -- If we arrive here, either the pattern is over (`Nothing`) or the next
            -- part of the pattern is not a word that starts with a hyphen.
            _ -> True


-- Preposition are a closed class, but this list is not yet exhaustive.
-- It can and should be extended when needed. The following list is a
-- selection of the prepositions found at
-- https://en.wikipedia.org/wiki/List_of_English_prepositions.
--
prepositions :: Set Text
prepositions = Set.fromList
    [ "about"
    , "above"
    , "across"
    , "after"
    , "against"
    , "along", "alongside"
    , "amid", "amidst"
    , "among"
    , "around"
    , "as"
    , "at"
    , "atop"
    , "before"
    , "behind"
    , "below"
    , "beneath"
    , "beside", "besides"
    , "between"
    , "beyond"
    , "but"
    , "by"
    , "except"
    , "for"
    , "from"
    , "in", "inside", "into"
    , "like"
    , "modulo", "mod"
    , "near"
    , "next"
    , "of"
    , "off"
    , "on"
    , "onto"
    , "opposite"
    , "out"
    , "over"
    , "past"
    , "per"
    , "sans"
    , "till"
    , "to"
    , "under"
    , "underneath"
    , "unlike"
    , "unto"
    , "up", "upon"
    , "versus"
    , "via"
    , "with"
    , "within"
    , "without"
    ]
