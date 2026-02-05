{-# LANGUAGE RecordWildCards #-}

module Encoding where


import Base
import Report.Location
import Syntax.Internal
import Syntax.Lexicon
import Tptp.UnsortedFirstOrder qualified as Tptp

import Bound
import Bound.Scope
import Data.Text qualified as Text
import TextBuilder


encodeTask :: Lexicon -> Task -> Tptp.Task
encodeTask l Task{..} = Tptp.Task (conjecture' : hypos')
    where
        conjecture' = encodeConjecture l taskConjectureLabel taskLocation taskDirectness taskConjecture
        hypos' = encodeHypos l taskHypotheses


encodeConjecture :: Lexicon -> Marker -> Location -> Directness -> Formula -> Tptp.AnnotatedFormula
encodeConjecture l (Marker str) loc directness f = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Conjecture (encodeExpr l f) case directness of
    Direct -> (Tptp.Source (locationToText loc))
    Indirect _ -> (Tptp.Source (locationToText loc <> " (indirect proof)"))

-- NOTE: E's SInE will only filter out axioms and leave hypotheses fixed.
encodeHypos :: Lexicon -> [(Marker, Formula)] -> [Tptp.AnnotatedFormula]
encodeHypos l phis = [makeHypo  m (encodeExpr l phi) | (m,  phi) <- phis]
    where
        makeHypo :: Marker -> TextBuilder -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Axiom f' (Tptp.Source "")

encodeWithRole :: Tptp.Role -> Lexicon -> [(Marker, Formula)] -> [Tptp.AnnotatedFormula]
encodeWithRole role l phis = [makeHypo  m (encodeExpr l phi) | (m,  phi) <- phis]
    where
        makeHypo :: Marker -> TextBuilder -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) role f' (Tptp.Source "")


encodeExpr :: Lexicon -> Expr -> TextBuilder
encodeExpr l = buildExpr . fmap encodeFreeVar
    where
    buildExpr :: ExprOf EncodedVar -> TextBuilder
    buildExpr = \case
        Equals _pos e1 e2 ->
            buildExpr e1 <> char '=' <> buildExpr e2
        NotEquals _pos e1 e2 ->
            buildExpr e1 <> text "!=" <> buildExpr e2
        Atomic _pos p es ->
            let p' = encodePredicate l p
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
            buildApply (encodeSymbol l symb) (buildExpr <$> es)
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




encodeSymbol :: Lexicon -> Symbol -> Tptp.AtomicWord
encodeSymbol l symb = atomicWordFromRightMarker case symb of
    SymbolMixfix op ->
        Right (mixfixMarker op)
    SymbolFun fun ->
        lookupLexicalItem fun (lexiconFuns l)
    SymbolInteger n ->
        Right (Marker (Text.pack (show n)))
    SymbolPredicate _ ->
        error "IMPOSSIBLE: predicates should already be translated"


encodePredicate :: Lexicon -> Predicate -> Tptp.AtomicWord
encodePredicate l p = atomicWordFromRightMarker case p of
    PredicateAdj adj ->
        lookupLexicalItem adj (lexiconAdjs l)
    PredicateVerb verb ->
        lookupLexicalItem verb (lexiconVerbs l)
    PredicateNoun noun ->
        lookupLexicalItem noun (lexiconNouns l)
    PredicateRelation rel ->
        lookupLexicalItem rel (lexiconRelationSymbols l)
    PredicateNounStruct noun ->
        lookupLexicalItem noun (lexiconStructNouns l)
    PredicateSymbol symb ->
        Right (Marker symb)


atomicWordFromRightMarker :: Either String Marker -> Tptp.AtomicWord
atomicWordFromRightMarker = \case
    Right (Marker m) -> Tptp.AtomicWord m
    Left a -> error ("symbol not in lexicon" <> a)

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
