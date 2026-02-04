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
import Data.HashSet qualified as Set
import Data.HashMap.Strict qualified as HM
import Data.Text qualified as Text
import Text.Earley.Mixfix (Holey, Associativity(..))


data Lexicon = Lexicon
    { lexiconMixfixTable        :: Seq (HashMap (Holey Token) Associativity)
    , lexiconMixfixMarkers      :: HashMap (Holey Token) Marker
    , lexiconConnectives        :: [[(Holey Token, Associativity)]]
    , lexiconPrefixPredicates   :: LexicalItems PrefixPredicate
    , lexiconStructFun          :: LexicalItems StructSymbol
    , lexiconRelationSymbols    :: LexicalItems RelationSymbol
    , lexiconVerbs              :: LexicalItems (SgPl LexicalPhrase)
    , lexiconAdjLs              :: LexicalItems LexicalPhrase
    , lexiconAdjRs              :: LexicalItems LexicalPhrase
    , lexiconNouns              :: LexicalItems (SgPl LexicalPhrase)
    , lexiconStructNouns        :: LexicalItems (SgPl LexicalPhrase)
    , lexiconFuns               :: LexicalItems (SgPl LexicalPhrase)
    } deriving (Show, Eq)

-- Projection returning the union of both left and right attributes.
--
lexiconAdjs :: Lexicon -> HashMap LexicalPhrase Marker
lexiconAdjs lexicon = lexiconAdjLs lexicon <> lexiconAdjRs lexicon

lookupOp :: FunctionSymbol -> HashMap (Holey Token) Marker-> Either String Marker
lookupOp f ops = case HM.lookup f ops of
    Just m -> Right m
    Nothing -> Left (show f)

lookupLexicalItem :: (Hashable a, Show a) => a -> LexicalItems a -> Either String Marker
lookupLexicalItem a items = case HM.lookup a items of
    Just m -> Right m
    Nothing -> Left (show a)

type LexicalItems a = HashMap a Marker

builtins :: Lexicon
builtins = Lexicon
    { lexiconMixfixTable        = builtinMixfixTable
    , lexiconMixfixMarkers      = builtinMixfixMarkers
    , lexiconPrefixPredicates   = builtinPrefixPredicates
    , lexiconStructFun          = builtinStructOps
    , lexiconConnectives        = builtinConnectives
    , lexiconRelationSymbols    = builtinRelationSymbols
    , lexiconAdjLs              = mempty
    , lexiconAdjRs              = builtinAdjRs
    , lexiconVerbs              = builtinVerbs
    , lexiconNouns              = builtinNouns
    , lexiconStructNouns        = builtinStructNouns
    , lexiconFuns               = mempty
    }

builtinMixfixMarkers :: HashMap FunctionSymbol Marker
builtinMixfixMarkers = HM.map snd (fold builtinMixfix)

builtinMixfixTable :: Seq (HashMap (Holey Token) Associativity)
builtinMixfixTable = fmap (HM.map fst) builtinMixfix

-- INVARIANT: 10 precedence levels for now.
builtinMixfix :: Seq (HashMap FunctionSymbol (Associativity, Marker))
builtinMixfix = Seq.fromList $ (HM.fromList <$>)
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
        builtinIdentifiers :: [(FunctionSymbol, (Associativity, Marker))]
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


prefixOps :: [(FunctionSymbol, (Associativity, Marker))]
prefixOps =
    [ ([Just (Command "rfrac"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "rfrac"))
    , ([Just (Command "exp"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "exp"))
    , ([Just (Command "unions"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "unions"))
    , ([Just (Command "cumul"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "cumul"))
    , ([Just (Command "fst"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "fst"))
    , ([Just (Command "snd"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "snd"))
    , ([Just (Command "pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "pow"))
    , ([Just (Command "neg"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "neg"))
    , ([Just (Command "inv"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "inv"))
    , ([Just (Command "abs"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR], (NonAssoc, "abs"))
    , (ConsSymbol, (NonAssoc, "cons"))
    , (PairSymbol, (NonAssoc, "pair"))
    -- NOTE Is now defined and hence no longer necessary , (ApplySymbol, (NonAssoc, "apply"))
    ]


builtinStructOps :: LexicalItems StructSymbol
builtinStructOps = HM.fromList
    [ (CarrierSymbol, "carrier")
    ]

identifier :: Text -> (Holey Token, (Associativity, Marker))
identifier cmd = ([Just (Command cmd)], (NonAssoc, Marker cmd))


builtinRelationSymbols :: LexicalItems RelationSymbol
builtinRelationSymbols = HM.fromList
    [ (Symbol "=", "eq")
    , (Command "rless", "rless")
    , (Command "neq", "neq")
    , (ElementSymbol, "elem")
    , (Command "notin", "notelem") -- Alternative to @\not\in@.
    ]

builtinPrefixPredicates :: LexicalItems PrefixPredicate
builtinPrefixPredicates = HM.fromList
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


binOp :: Token -> Associativity -> Marker -> (Holey Token, (Associativity, Marker))
binOp tok assoc m = ([Nothing, Just tok, Nothing], (assoc, m))

binOp' :: Token -> Associativity -> (Holey Token, Associativity)
binOp' tok assoc = ([Nothing, Just tok, Nothing], assoc)

builtinAdjRs :: LexicalItems LexicalPhrase
builtinAdjRs = HM.fromList
    [ (unsafeReadPhrase "equal to ?", "eq")
    ]

builtinVerbs :: LexicalItems (SgPl LexicalPhrase)
builtinVerbs = HM.fromList
    [ (unsafeReadPhraseSgPl "equal[s/] ?", "eq")
    ]


-- Some of these do/should correspond to mathlib structures,
-- e.g.: lattice, complete lattice, ring, etc.
--
builtinNouns :: LexicalItems (SgPl LexicalPhrase)
builtinNouns = HM.mapKeys unsafeReadPhraseSgPl (HM.fromList
    -- Nullary
    [ ("set[/s]", "set")
    , ("point[/s]", "point")
    , ("element[/s] of ?", "elem")
    ])

_Onesorted :: SgPl LexicalPhrase
_Onesorted = unsafeReadPhraseSgPl "onesorted structure[/s]"

builtinStructNouns :: LexicalItems (SgPl LexicalPhrase)
builtinStructNouns = HM.singleton _Onesorted "onesorted_structure"


-- | Naïve splitting of lexical phrases to insert a variable slot for names in noun phrases,
-- as in /@there exists a linear form $h$ on $E$@/, where the underlying pattern is
-- /@linear form on ?@/. In this case we would get:
--
-- > splitOnVariableSlot (sg (unsafeReadPhraseSgPl "linear form[/s] on ?"))
-- > ==
-- > (unsafeReadPhrase "linear form", unsafeReadPhrase "on ?")
--
splitOnVariableSlot :: LexicalPhrase -> (LexicalPhrase, LexicalPhrase)
splitOnVariableSlot phrase = case prepositionIndices <> nonhyphenatedSlotIndices of
    [] -> (phrase, []) -- Place variable slot at the end.
    is -> List.splitAt (minimum is) phrase
    where
        prepositionIndices, slotIndices, nonhyphenatedSlotIndices :: [Int] -- Ascending.
        prepositionIndices = List.findIndices isPreposition phrase
        slotIndices = List.findIndices isNothing phrase
        nonhyphenatedSlotIndices = [i | i <- slotIndices, noHyphen (nth (i + 1) phrase)]

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
prepositions :: HashSet Text
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
