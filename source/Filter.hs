module Filter where


import Base
import Syntax.Internal

import Data.Set qualified as Set
import Data.Map qualified as Map
import GHC.Float (int2Float)
import Bound.Scope


convergence :: Float
convergence = 2.8


passmark :: Float
passmark = 0.4


filterTask :: Task -> Task
filterTask Task{taskDirectness = directness, taskConjectureLabel = label, taskConjecture = conjecture, taskHypotheses = hypotheses} =
    let
        motive = case directness of
            Indirect formerConjecture -> formerConjecture
            Direct -> conjecture
        filteredHypos = if length hypotheses < 20
            then hypotheses
            else Map.keys (relevantFacts passmark motive (Set.fromList hypotheses))
    in Task
        { taskDirectness = directness
        , taskConjecture = conjecture
        , taskHypotheses = filteredHypos
        , taskConjectureLabel = label
        }


relevantFacts :: Float -> ExprOf a -> Set (Marker, Expr) -> Map (Marker, Expr) Float
relevantFacts p conjecture cs = relevantClausesNaive p (symbols conjecture) cs Map.empty


relevantClausesNaive
    :: Float -- ^ Pass mark
    -> Set Symbol -- ^ Relevant symbols
    -> Set (Marker, Expr) -- ^ working irrelevant facts
    -> Map (Marker, Expr) Float -- ^ Accumulator of relevant facts
    -> Map (Marker, Expr) Float -- ^ Final relevant facts
relevantClausesNaive p rs cs a =
    let ms = Map.fromSet (clauseMarkNaive rs) cs
        rels = Map.filter (p <=) ms
        cs' = Map.keysSet (Map.difference ms rels)
        p' = p + (1 - p) / convergence
        a' = a `Map.union` rels
        rs' = Set.unions (Set.map (symbols . snd) (Map.keysSet rels)) `Set.union` rs
    in
        if Map.null rels
            then a
            else relevantClausesNaive p' rs' cs' a'


clauseMarkNaive
    :: Set Symbol
    -> (Marker, Expr)
    -> Float
clauseMarkNaive rs c =
    let cs = symbols (snd c)
        r = cs `Set.intersection` rs
        ir = cs `Set.difference` r
    in int2Float (Set.size r) / int2Float (Set.size r + Set.size ir)


clauseMark :: Set Symbol -> ExprOf a -> Map Symbol Int -> Float
clauseMark rs c ftab =
    let cs = symbols c
        r = cs `Set.intersection` rs
        ir = cs `Set.difference` r
        m = sum (Set.map (ftab `funWeight`) r)
    in m / (m + int2Float (Set.size ir))


funWeight :: Map Symbol Int -> Symbol -> Float
funWeight ftab f = weightFromFrequency (Map.lookup f ftab ?? 0)


weightFromFrequency :: Int -> Float
weightFromFrequency n = 1 + 2 / log (int2Float n + 1)


symbols :: ExprOf a -> Set Symbol
symbols = \case
    TermVar{} -> Set.empty
    TermSymbol _pos sym es -> Set.insert sym (Set.unions (fmap symbols es))
    TermSep _ e scope -> symbols e `Set.union` symbols (fromScope scope)
    ReplacePred _ _ e scope -> symbols e `Set.union` symbols (fromScope scope)
    ReplaceFun es scope cond -> (Set.unions (fmap (symbols . snd) es)) `Set.union` symbols (fromScope scope) `Set.union` symbols (fromScope cond)
    Connected _ e1 e2 -> symbols e1 `Set.union` symbols e2
    Lambda scope -> symbols (fromScope scope)
    Quantified _ scope -> symbols (fromScope scope)
    PropositionalConstant{} -> Set.empty
    Not _pos e -> symbols e
    _ -> error "Filter.symbols"

symbolTable :: ExprOf a -> Map Symbol Int
symbolTable = \case
    TermVar{} -> Map.empty
    TermSymbol _pos sym es -> insert sym 1 (unions (fmap symbolTable es))
    TermSep _ e scope -> symbolTable e `union` symbolTable (fromScope scope)
    ReplacePred _ _ e scope -> symbolTable e `union` symbolTable (fromScope scope)
    ReplaceFun es scope cond -> (unions (fmap (symbolTable . snd) (toList es))) `union` symbolTable (fromScope scope) `union` symbolTable (fromScope cond)
    Connected _ e1 e2 -> symbolTable e1 `union` symbolTable e2
    Lambda scope -> symbolTable (fromScope scope)
    Quantified _ scope -> symbolTable (fromScope scope)
    PropositionalConstant{} -> Map.empty
    Not _pos e -> symbolTable e
    _ -> error "Filter.symbolTable"
    where
        union = Map.unionWith (+)
        unions = Map.unionsWith (+)
        insert = Map.insertWith (+)
