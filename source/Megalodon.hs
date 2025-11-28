module Megalodon where

import Base hiding (null)
import Syntax.Internal
import Syntax.Lexicon
import Checking (makeReplacementIff)

import Bound.Scope
import Bound.Var
import Data.HashMap.Strict qualified as HM
import Data.List.NonEmpty qualified as NonEmpty
import TextBuilder
import Data.List qualified as List
import Data.Text qualified as Text


encodeBlocks :: Lexicon -> [Block] -> Text
encodeBlocks lexi blocks = TextBuilder.toText (preamble <> buildBlocks lexi blocks)

closure :: [ExprOf VarSymbol] -> ExprOf VarSymbol -> Formula
closure asms stmt = contraction (forallClosure mempty (makeConjunction asms `Implies` stmt))

unAsm :: Asm -> Formula
unAsm (Asm phi) = phi
unAsm (AsmStruct x sp) = TermSymbol (SymbolPredicate (PredicateNounStruct sp)) [TermVar x]

buildBlocks :: Lexicon -> [Block] -> TextBuilder
buildBlocks lexi = \case
    BlockAxiom _pos lbl (Axiom asms stmt) : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Fact " <> buildMarker lbl <> text " : " <> buildFormula lexi phi <> text ".\nAdmitted.\n" <> buildBlocks lexi blocks
    BlockLemma _pos lbl (Lemma asms stmt) : BlockProof _ _ : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Theorem " <> buildMarker lbl <> text " : " <> buildFormula lexi phi <> text ".\nAdmitted.\n" <> buildBlocks lexi blocks
    BlockLemma _pos lbl (Lemma asms stmt) : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Theorem " <> buildMarker lbl <> text " : " <> buildFormula lexi phi <> text ".\nAdmitted.\n" <> buildBlocks lexi blocks
    BlockDefn _pos _lbl defn : blocks->
        buildDefn lexi defn <> buildBlocks lexi blocks
    BlockAbbr _pos _lbl abbr : blocks->
        buildAbbr lexi abbr <> buildBlocks lexi blocks
    [] ->
        mempty
    block : _ ->
        _TODO ("builBlocks" <> show block)

buildDefn :: Lexicon -> Defn -> TextBuilder
buildDefn lexi = \case
    DefnPredicate [] predi xs phi ->
        "Definition " <> buildSymbol lexi (SymbolPredicate predi) <> " := " <>
        "fun " <> buildVarSymbols xs <> ": set => " <> buildFormula lexi phi <> ".\n"
    DefnFun [] f xs phi ->
        "Definition " <> buildSymbol lexi (SymbolFun f) <> " := " <>
        buildSetFunIfNonEmpty (buildVarSymbols xs) (buildFormula lexi phi) <> ".\n"
    DefnOp f xs phi ->
        "Definition " <> buildSymbol lexi (SymbolMixfix f) <> " := " <>
        buildSetFunIfNonEmpty (buildVarSymbols xs) (buildFormula lexi phi) <> ".\n"
    _ ->
        error "assumptions in definition, deprecated"

buildAbbr :: Lexicon -> Abbreviation -> TextBuilder
buildAbbr lexi (Abbreviation f body) =
    "Definition " <> buildSymbol lexi f <> " := " <>
    buildSetFunIfNonEmpty buildBindings' (buildFormula lexi ((instantiate (TermVar . FreshVar) (fmap absurd body)))) <> ".\n"
        where
            buildBindings' :: TextBuilder
            buildBindings' = intercalate (char ' ') (buildVarSymbol . FreshVar <$> List.sort (List.nub (bindings body)))

buildSetFunIfNonEmpty :: TextBuilder -> TextBuilder -> TextBuilder
buildSetFunIfNonEmpty xs b = if isEmpty xs then b else "fun " <> xs <> " : set => " <> b

buildFormula :: Lexicon -> Formula -> TextBuilder
buildFormula lexi = \case
    TermVar x -> buildVarSymbol x
    -- We handle eq in a special manner to avoid having to specify the type of the equality.
    TermSymbol f [x,y] | isEqSymbol f ->
        char '(' <> buildFormula lexi x <> text " = " <> buildFormula lexi y <> char ')'
    TermSymbol f [x,y] | isDiseqSymbol f ->
        char '(' <> buildFormula lexi x <> text " <> " <> buildFormula lexi y <> char ')'
    TermSymbol f es ->
        let es' = buildSymbol lexi f : (buildFormula lexi <$> es)
        in char '(' <> intercalate (char ' ') es' <> char ')'
    Apply e es ->
        let es' = NonEmpty.cons (buildFormula lexi e) (buildFormula lexi <$> es)
        in char '(' <> intercalate (char ' ') es' <> char ')'
    Not e -> text "~(" <> buildFormula lexi e <> char ')'
    Connected conn e1 e2 ->
        char '(' <> buildConn conn (buildFormula lexi e1) (buildFormula lexi e2) <> char ')'
    Quantified quant body ->
        char  '(' <> buildQuant quant <> char ' ' <> buildBindings body <> text ",(" <> buildFormula lexi (instantiate TermVar body) <> text "))"
    TermSep x bound phi ->
        char '{' <> buildVarSymbol x <> " :e (" <> buildFormula lexi bound <> text ")|" <> buildFormula lexi (instantiate1 (TermVar x) phi) <> char '}'
    Iota _ _ -> error "TODO buildFormula Iota"
    ReplacePred y x xB body ->
        let x' = buildVarSymbol x
            y' = buildVarSymbol y
            fromReplacementVar = \case
                ReplacementDomVar -> TermVar x
                ReplacementRangeVar -> TermVar y
            body' = buildFormula lexi (instantiate fromReplacementVar body)
        in "let MkReplFun := fun " <> x' <> " : set => (Eps_i (fun " <> y' <> "=>" <> body' <> ")) in {MkReplFun " <> x' <> "|" <> x' <> " :e (" <> buildFormula lexi xB <> ")}"
    ReplaceFun ((x, xB) :| []) lhs cond ->
        let x' = buildVarSymbol x
            xB' = "(" <> buildFormula lexi xB <> ")" -- parens probably not needed
            lhs' = "(fun " <> x' <> " => " <> buildFormula lexi (instantiate TermVar lhs) <> ")"
            cond' = "(fun " <> x' <> " => " <> buildFormula lexi (instantiate TermVar cond) <> ")"
        -- Using "ReplSep : set->(set->prop)->(set->set)->set"
        in "ReplSep " <> xB' <> cond' <> lhs'
    ReplaceFun ((x, xB) :| (y, yB) : []) lhs cond ->
        let x' = buildVarSymbol x
            xB' = "(" <> buildFormula lexi xB <> ")"
            y' = buildVarSymbol y
            yB' = "(fun dummyVar => " <> buildFormula lexi yB <> ")"
            lhs' = "(fun " <> x' <> " " <> y' <> " => " <> buildFormula lexi (instantiate TermVar lhs) <> ")"
            cond' = "(fun " <> x' <> " " <> y' <> " => " <> buildFormula lexi (instantiate TermVar cond) <> ")"
        -- Using "ReplSep2 : set -> (set -> set) -> (set -> set -> prop) -> (set -> set -> set) -> set"
        in "ReplSep2 " <> xB' <> yB' <> cond' <> lhs'
    ReplaceFun bounds lhs cond ->
        -- Silly placeholder translation for now
        let iff = makeReplacementIff (TermVar (F "frs")) bounds lhs cond
        in "Eps_i (fun frs : set => " <> buildFormula lexi iff <> ")"
    Lambda _ -> text "TODO_buildFormula_Lambda"
    PropositionalConstant IsTop -> "True"
    PropositionalConstant IsBottom -> "False"
    TermSymbolStruct f me ->
        let f' = buildMarker ((?? error "unrecognized symbol") (HM.lookup f (lexiconStructFun lexi)))
            e = me ?? error "unannotated struct op"
        in char '(' <> f' <> buildFormula lexi e <> char ')'

buildMarker :: Marker -> TextBuilder
buildMarker (Marker m)= text m

buildQuant :: Quantifier -> TextBuilder
buildQuant = \case
    Universally -> "forall"
    Existentially -> "exists"

buildBindings :: Scope VarSymbol ExprOf a -> TextBuilder
buildBindings body = intercalate (char ' ') (buildVarSymbol <$> List.nub (bindings body))

buildBounds :: Lexicon -> NonEmpty (VarSymbol, ExprOf VarSymbol) -> TextBuilder
buildBounds l (bound :| bounds) = foldr (\b bs -> buildBound b <> "/\\ " <> bs) (buildBound bound) bounds
    where
        buildBound (y, yB) = buildVarSymbol y <> " :e (" <> buildFormula l yB <> ")"

buildConn :: Connective -> (TextBuilder -> TextBuilder -> TextBuilder)
buildConn conn = \p q -> case conn of
    Conjunction -> p <> text "/\\" <> q
    Disjunction -> p <> text "\\/" <> q
    Implication -> p <> text "->" <> q
    Equivalence -> p <> text "<->" <> q
    ExclusiveOr -> text "xor" <> p <> char ' ' <> q
    NegatedDisjunction -> text "nor" <> p <> char ' ' <> q

buildVarSymbol :: VarSymbol -> TextBuilder
buildVarSymbol = \case
    NamedVar x -> text x
    FreshVar i -> char 'x' <> decimal i

buildVarSymbols :: (Functor t, Foldable t) => t VarSymbol -> TextBuilder
buildVarSymbols xs = intercalate (char ' ') (fmap buildVarSymbol xs)

buildSymbol :: Lexicon -> Symbol -> TextBuilder
buildSymbol _ (SymbolInteger i) = decimal i
buildSymbol lexi symb = fromRightMarker case symb of
    SymbolMixfix f ->
        lookupOp f (lexiconMixfix lexi)
    SymbolFun f -> lookupLexicalItem f (lexiconFuns lexi)
    SymbolPredicate (PredicateAdj f) -> lookupLexicalItem f (lexiconAdjs lexi)
    SymbolPredicate (PredicateVerb f) -> lookupLexicalItem f (lexiconVerbs lexi)
    SymbolPredicate (PredicateNoun f) -> lookupLexicalItem f (lexiconNouns lexi)
    SymbolPredicate (PredicateRelation f) ->lookupLexicalItem f (lexiconRelationSymbols lexi)
    SymbolPredicate (PredicateNounStruct f) -> lookupLexicalItem f (lexiconStructNouns lexi)
    SymbolPredicate (PredicateSymbol f) -> Right (Marker f) -- HM.lookup f (lexiconPrefixPredicates lexi)


fromRightMarker :: Either String Marker -> TextBuilder
fromRightMarker = \case
    Right (Marker m) -> text m
    Left a -> error ("symbol not in lexicon" <> a)

isEqSymbol :: Symbol -> Bool
isEqSymbol = \case
    SymbolPredicate (PredicateRelation (Symbol "=")) -> True
    SymbolPredicate (PredicateVerb f) | f == (unsafeReadPhraseSgPl "equal[s/] ?") -> True
    SymbolPredicate (PredicateAdj f) | f == (unsafeReadPhrase "equal to ?") -> True
    _ -> False

isDiseqSymbol :: Symbol -> Bool
isDiseqSymbol = \case
    SymbolPredicate (PredicateRelation (Command "neq")) -> True
    SymbolPredicate (PredicateAdj f) | f == (unsafeReadPhrase "distinct from ?") -> True
    _ -> False

preamble :: TextBuilder
preamble = text $ Text.unlines
    [ "Let emptyset : set := Empty."
    , "Let elem : set->set->prop := In."
    , "Let notelem : set->set->prop := fun a A => ~(In a A)."
    , "Let pow : set->set := Power."
    , "Let unions : set->set := Union."
    , "Let union : set->set->set := binunion."
    , "Let cons : set -> set -> set := fun x X => binunion {x} X."
    , "Let xor : prop -> prop -> prop := fun p q =>  (p \\/ q) /\\ ~(p /\\ q)."
    , "Let pair : set -> set -> set := fun a b => {{a}, {a, b}}."
    , "Let fst : set -> set := fun p => Eps_i (fun a => exists b, p = pair a b)."
    , "Let snd : set -> set := fun p => Eps_i (fun b => exists a, p = pair a b)."
    , "Let nor : prop -> prop -> prop := fun p q => ~(p \\/ q) ."
    ]
