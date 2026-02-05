{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}


module Tptp.SmtLib where
-- ^ Export tasks to SMT-LIB S-expressions.

import Base
import Encoding qualified
import Syntax.Internal
import Tptp.UnsortedFirstOrder qualified as Tptp

import Bound
import Bound.Scope
import Data.Text qualified as Text
import TextBuilder

buildList :: [TextBuilder] -> TextBuilder
buildList bs = char '(' <> intercalate (char ' ') bs <> char ')'
{-# INLINE buildList #-}

quotedAtom :: TextBuilder -> TextBuilder
quotedAtom b = char '|' <> b <> char '|'
{-# INLINE quotedAtom #-}

buildAtomicWord :: Tptp.AtomicWord -> TextBuilder
buildAtomicWord (Tptp.AtomicWord w) = if Tptp.isProperAtomicWord w then text w else quotedAtom (text w)

buildVariable :: Tptp.Variable -> TextBuilder
buildVariable (Tptp.Variable v) = text (Text.replace "'" "_" v)

buildApply :: Tptp.AtomicWord -> [TextBuilder] -> TextBuilder
buildApply f args = case args of
    [] -> buildAtomicWord f
    _ -> buildList (buildAtomicWord f : args)

encodeTask :: Task -> TextBuilder
encodeTask Task{..} = buildTask (conjecture' : hypos')
    where
        conjecture' = encodeExpr taskConjecture
        hypos' = encodeExpr . hypothesisFormula . snd <$> taskHypotheses

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
            let p' = Encoding.encodePredicate p
                es' = buildExpr <$> toList es
            in buildApply p' es'
        PropositionalConstant IsBottom ->
            text "$false"
        PropositionalConstant IsTop ->
            text "$true"
        Not _pos f ->
            text "(not " <> buildExpr f <> char ')'
        Connected Conjunction f1 f2 ->
            text "(and  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
        Connected Disjunction f1 f2 ->
            text "(or  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
        Connected Implication f1 f2 ->
            text "(=>  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
        Connected Equivalence f1 f2 ->
            text "(=  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
        Connected NegatedDisjunction f1 f2 ->
            text "(not " <> buildExpr (Connected Disjunction f1 f2) <> char ')'
        Connected ExclusiveOr f1 f2 ->
            text "(not " <> buildExpr (Connected Equivalence f1 f2) <> char ')'
        Quantified quant scope ->
            buildQuantified quant scope
        TermVar v ->
            buildTermVar v
        Apply e es -> case e of
            TermVar (FreeConst x) -> buildApply x (buildExpr <$> toList es)
            _ -> error ("encodeExpr: complex term as head of applicaition: " <> show e)
        TermSymbol _pos symb es ->
            buildApply (Encoding.encodeSymbol symb) (buildExpr <$> es)
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
        BoundVar v -> buildVariable v
        FreeConst w -> buildAtomicWord w

    buildQuantified :: Quantifier -> Scope VarSymbol ExprOf EncodedVar -> TextBuilder
    buildQuantified quant scope =
        let phi = instantiate instantiator scope
            xs = [Encoding.encodeBoundVar x | x <- nubOrd (bindings scope)]
        in case xs of
            [] -> buildExpr phi
            _ -> buildQuantifier quant <> char ' ' <> buildList (map buildVariable xs) <> char ' ' <> buildExpr phi

    buildQuantifier :: Quantifier -> TextBuilder
    buildQuantifier = \case
        Universally -> "(forall "
        Existentially -> "(exists "

instantiator :: VarSymbol -> ExprOf EncodedVar
instantiator bv = TermVar (BoundVar (Encoding.encodeBoundVar bv))

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

buildAnnotatedFormula :: TextBuilder -> TextBuilder
buildAnnotatedFormula phi = "(assert " <> phi <> char ')'

buildTask :: [TextBuilder] -> TextBuilder
buildTask fofs = intercalate (char '\n') decls <> "\n(check-sat)\n"
    where
        decls = "(set-logic UF)" : map buildAnnotatedFormula fofs
