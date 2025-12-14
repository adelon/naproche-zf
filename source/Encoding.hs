{-# LANGUAGE RecordWildCards #-}

module Encoding where


import Base
import Report.Location
import Syntax.Internal
import Syntax.Lexicon
import Tptp.UnsortedFirstOrder qualified as Tptp

import Data.Text qualified as Text
import Bound
import Bound.Scope


encodeTask :: Lexicon -> Task -> Tptp.Task
encodeTask l Task{..} = Tptp.Task (conjecture' : hypos')
    where
        conjecture' = encodeConjecture l taskConjectureLabel taskLocation taskConjecture
        hypos' = encodeHypos l taskHypotheses


encodeConjecture :: Lexicon -> Marker -> Location -> Formula -> Tptp.AnnotatedFormula
encodeConjecture l (Marker str) loc f = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Conjecture (encodeExpr l f) (Tptp.Source (locationToText loc))

-- NOTE: E's SInE will only filter out axioms and leave hypotheses fixed.
encodeHypos :: Lexicon -> [(Marker, Formula)] -> [Tptp.AnnotatedFormula]
encodeHypos l phis = [makeHypo  m (encodeExpr l phi) | (m,  phi) <- phis]
    where
        makeHypo :: Marker -> Tptp.Expr -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) Tptp.Axiom f' (Tptp.Source "")

encodeWithRole :: Tptp.Role -> Lexicon -> [(Marker, Formula)] -> [Tptp.AnnotatedFormula]
encodeWithRole role l phis = [makeHypo  m (encodeExpr l phi) | (m,  phi) <- phis]
    where
        makeHypo :: Marker -> Tptp.Expr -> Tptp.AnnotatedFormula
        makeHypo (Marker str) f' = Tptp.AnnotatedFormula (Tptp.NameAtomicWord (Tptp.AtomicWord str)) role f' (Tptp.Source "")


encodeExpr :: Lexicon -> Expr -> Tptp.Expr
encodeExpr l = go . (fmap encodeFreeVar)
    where
    go :: ExprOf Tptp.Expr -> Tptp.Expr
    go = \case
        Equals _pos e1 e2 ->
            Tptp.Eq (go e1) (go e2)
        NotEquals _pos e1 e2 ->
            Tptp.NotEq (go e1) (go e2)
        Atomic _pos p es ->
            let p' = encodePredicate l p
                es' = go <$> toList es
            in Tptp.Apply p' es'
        PropositionalConstant IsBottom ->
            Tptp.Bottom
        PropositionalConstant IsTop ->
            Tptp.Top
        Not _pos f ->
            Tptp.Not (go f)
        Connected Conjunction f1 f2 ->
            Tptp.Conn Tptp.And (go f1) (go f2)
        Connected Disjunction f1 f2 ->
            Tptp.Conn Tptp.Or (go f1) (go f2)
        Connected Implication f1 f2 ->
            Tptp.Conn Tptp.Imply (go f1) (go f2)
        Connected Equivalence f1 f2 ->
            Tptp.Conn Tptp.Iff (go f1) (go f2)
        Connected NegatedDisjunction f1 f2 ->
            Tptp.Not (Tptp.Conn Tptp.Or (go f1) (go f2))
        Connected ExclusiveOr f1 f2 ->
            Tptp.Not (Tptp.Conn Tptp.Iff (go f1) (go f2))
        Quantified quant scope ->
            let phi = instantiate instantiator scope
                xs = [encodeBoundVar x | x <- nubOrd (bindings scope)]
                phi' = go phi
                quant' = encodeQuant quant
            in case xs of
                [] -> phi'
                y:ys -> Tptp.Quantified quant' (y:|ys) phi'
        TermVar v ->
            v
        Apply e es -> case e of
            TermVar (Tptp.Const x) -> Tptp.Apply x (go <$> toList es)
            _ -> error ("encodeExpr: complex term as head of applicaition: " <> show e)
        TermSymbol _pos symb es ->
            Tptp.Apply (encodeSymbol l symb) (go <$> es)
        e@ReplaceFun{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        e@ReplacePred{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        e@TermSep{} ->
            error ("Precondition failed in encodeTerm, cannot encode terms with comprehensions directly: " <> show e)
        TermSymbolStruct symb e -> case e of
            Just e' ->
                Tptp.Apply (Tptp.AtomicWord ("s__" <> (unStructSymbol symb))) [go e']
            Nothing ->
                error ("encodeExpr.go (precondition failed): unannotated struct symbol" <> show symb)
        _ -> error "encodeExpr.go: missing case"


instantiator :: VarSymbol -> ExprOf Tptp.Expr
instantiator bv = TermVar (Tptp.Var (encodeBoundVar bv))



encodeQuant :: Quantifier -> Tptp.Quantifier
encodeQuant Universally = Tptp.Forall
encodeQuant Existentially = Tptp.Exists




encodeSymbol :: Lexicon -> Symbol -> Tptp.AtomicWord
encodeSymbol l symb = atomicWordFromRightMarker case symb of
    SymbolMixfix op ->
        lookupOp op (lexiconMixfix l)
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

encodeFreeVar :: VarSymbol -> Tptp.Expr
encodeFreeVar fv = Tptp.Const fv'
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
