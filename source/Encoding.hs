{-# LANGUAGE RecordWildCards #-}

module Encoding where


import Base
import Report.Location
import Syntax.Internal
import Tptp.UnsortedFirstOrder qualified as Tptp

import Bound
import Bound.Scope
import Data.Text qualified as Text
import TextBuilder


encodeTask :: Task -> Tptp.Task
encodeTask Task{..} = Tptp.Task (conjecture' : hypos')
    where
        conjecture' = encodeConjecture taskConjectureLabel taskLocation taskDirectness taskConjecture
        hypos' = encodeHypos taskHypotheses

encodeHypothesis :: Formula -> EncodedHypothesis
encodeHypothesis phi = EncodedHypothesis phi (encodeExpr (contraction phi))

-- | Boolean contraction of a task.
contractionTask :: Task -> Task
contractionTask task = task
    { taskConjecture = contraction (taskConjecture task)
    }


encodeConjecture :: Marker -> Location -> Directness -> Formula -> Tptp.AnnotatedFormula
encodeConjecture (Marker str) loc directness f = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Conjecture (encodeExpr f) case directness of
    Direct -> (Tptp.Source (locationToText loc))
    Indirect _ -> (Tptp.Source (locationToText loc <> " (indirect proof)"))

-- NOTE: E's SInE will only filter out axioms and leave hypotheses fixed.
encodeHypos :: [Hypothesis] -> [Tptp.AnnotatedFormula]
encodeHypos phis = [makeHypo  m (hypothesisEncoded hypo) | (m,  hypo) <- phis]
    where
        makeHypo :: Marker -> TextBuilder -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Axiom f' (Tptp.Source "")

encodeWithRole :: Tptp.Role -> [Hypothesis] -> [Tptp.AnnotatedFormula]
encodeWithRole role phis = [makeHypo  m (hypothesisEncoded hypo) | (m,  hypo) <- phis]
    where
        makeHypo :: Marker -> TextBuilder -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) role f' (Tptp.Source "")


encodeExpr :: Expr -> TextBuilder
encodeExpr = buildExpr . fmap encodeFreeVar
    where
    buildExpr :: ExprOf EncodedVar -> TextBuilder
    buildExpr = \case
        Equals _pos e1 e2 ->
            buildExpr e1 <> char '=' <> buildExpr e2
        NotEquals _pos e1 e2 ->
            buildExpr e1 <> text "!=" <> buildExpr e2
        Atomic _pos p es ->
            let p' = encodePredicate p
                es' = buildExpr <$> toList es
            in buildApply p' es'
        PropositionalConstant IsBottom ->
            text "$false"
        PropositionalConstant IsTop ->
            text "$true"
        Not _pos f ->
            char '~' <> buildUnitary f
        Connected Conjunction f1 f2 ->
            buildAnd f1 <> char '&' <> buildAnd f2
        Connected Disjunction f1 f2 ->
            buildOr f1 <> char '|' <> buildOr f2
        Connected Implication f1 f2 ->
            buildUnitary f1 <> text "=>" <> buildUnitary f2
        Connected Equivalence f1 f2 ->
            buildUnitary f1 <> text "<=>" <> buildUnitary f2
        Connected NegatedDisjunction f1 f2 ->
            char '~' <> buildUnitary (Connected Disjunction f1 f2)
        Connected ExclusiveOr f1 f2 ->
            char '~' <> buildUnitary (Connected Equivalence f1 f2)
        Quantified quant scope ->
            buildQuantified buildExpr buildUnitary quant scope
        TermVar v ->
            buildTermVar v
        Apply e es -> case e of
            TermVar (FreeConst x) -> buildApply x (buildExpr <$> toList es)
            _ -> error ("encodeExpr: complex term as head of applicaition: " <> show e)
        TermSymbol _pos symb es ->
            buildApply (encodeSymbol symb) (buildExpr <$> es)
        e@ReplaceFun{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        e@ReplacePred{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        e@TermSep{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        TermSymbolStruct symb e -> case e of
            Just e' ->
                buildApply (Tptp.AtomicWord ("s__" <> (unStructSymbol symb))) [buildExpr e']
            Nothing ->
                error ("encodeExpr.go (precondition failed): unannotated struct symbol" <> show symb)
        _ -> error "encodeExpr.go: missing case"

    buildTermVar :: EncodedVar -> TextBuilder
    buildTermVar = \case
        BoundVar v -> Tptp.buildVariable v
        FreeConst w -> Tptp.buildAtomicWord w

    buildApply :: Tptp.AtomicWord -> [TextBuilder] -> TextBuilder
    buildApply f args = case args of
        [] -> Tptp.buildAtomicWord f
        _ -> Tptp.buildAtomicWord f <> Tptp.buildTuple args

    isAtom :: ExprOf EncodedVar -> Bool
    isAtom = \case
        TermVar{} -> True
        TermSymbol{} -> True
        TermSymbolStruct{} -> True
        Apply{} -> True
        PropositionalConstant{} -> True
        Equals{} -> True
        NotEquals{} -> True
        _ -> False

    buildQuantified
        :: (ExprOf EncodedVar -> TextBuilder)
        -> (ExprOf EncodedVar -> TextBuilder)
        -> Quantifier
        -> Scope VarSymbol ExprOf EncodedVar
        -> TextBuilder
    buildQuantified renderEmpty renderBody quant scope =
        let phi = instantiate instantiator scope
            xs = [encodeBoundVar x | x <- nubOrd (bindings scope)]
        in case xs of
            [] -> renderEmpty phi
            _ -> buildQuantifier quant <> Tptp.buildList (map Tptp.buildVariable xs) <> char ':' <> renderBody phi

    buildQuantifier :: Quantifier -> TextBuilder
    buildQuantifier = \case
        Universally -> text "!"
        Existentially -> text "?"

    buildUnitary :: ExprOf EncodedVar -> TextBuilder
    buildUnitary = \case
        atom | isAtom atom -> buildExpr atom
        Quantified quant scope -> buildQuantified buildUnitary buildUnitary quant scope
        Not _ phi -> char '~' <> buildUnitary phi
        phi -> char '(' <> buildExpr phi <> char ')'

    buildAnd :: ExprOf EncodedVar -> TextBuilder
    buildAnd = \case
        Connected Conjunction f1 f2 -> buildAnd f1 <> char '&' <> buildAnd f2
        f -> buildUnitary f

    buildOr :: ExprOf EncodedVar -> TextBuilder
    buildOr = \case
        Connected Disjunction f1 f2 -> buildOr f1 <> char '|' <> buildUnitary f2
        f -> buildUnitary f


instantiator :: VarSymbol -> ExprOf EncodedVar
instantiator bv = TermVar (BoundVar (encodeBoundVar bv))




encodeSymbol :: Symbol -> Tptp.AtomicWord
encodeSymbol = \case
    SymbolMixfix op ->
        unMarker (mixfixMarker op)
    SymbolFun fun ->
        unMarker (lexicalItemSgPlMarker fun)
    SymbolInteger n ->
        unMarker (Marker (Text.pack (show n)))
    SymbolPredicate _ ->
        error "IMPOSSIBLE: predicates should already be translated"


encodePredicate :: Predicate -> Tptp.AtomicWord
encodePredicate = \case
    PredicateAdj adj ->
        unMarker (lexicalItemMarker adj)
    PredicateVerb verb ->
        unMarker (lexicalItemSgPlMarker verb)
    PredicateNoun noun ->
        unMarker (lexicalItemSgPlMarker noun)
    PredicateRelation rel ->
        unMarker (relationSymbolMarker rel)
    PredicateNounStruct noun ->
        unMarker (lexicalItemSgPlMarker noun)
    PredicateSymbol symb ->
        unMarker (Marker symb)

unMarker :: Marker -> Tptp.AtomicWord
unMarker (Marker m) = Tptp.AtomicWord m



data EncodedVar
    = BoundVar Tptp.Variable
    | FreeConst Tptp.AtomicWord
    deriving (Show, Eq, Ord)

encodeFreeVar :: VarSymbol -> EncodedVar
encodeFreeVar fv = FreeConst fv'
    where
        fv' = Tptp.AtomicWord case fv of
            NamedVar x -> Text.cons 'f' x
            FreshVar n -> Text.cons 'y' (Text.pack (show n))


-- | Tptp variables must be "upper words", starting with an uppercase letter
-- and continuing with alphanumeric characters. We prefix all variables
-- with "X" to make them easy to decode.
encodeBoundVar :: VarSymbol -> Tptp.Variable
encodeBoundVar bv = Tptp.Variable $ Text.cons 'X' case bv of
    NamedVar x -> x
    FreshVar n -> Text.pack (show n)
