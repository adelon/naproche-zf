module Megalodon where

import Base hiding (null)
import Syntax.Internal
import Checking (makeReplacementIff)
import Report.Location

import Bound.Scope
import Bound.Var
import Data.List.NonEmpty qualified as NonEmpty
import TextBuilder
import Data.List qualified as List
import Data.Text qualified as Text


encodeBlocks :: [Block] -> Text
encodeBlocks blocks = TextBuilder.toText (preamble <> buildBlocks blocks)

closure :: [ExprOf VarSymbol] -> ExprOf VarSymbol -> Formula
closure asms stmt = contraction (forallClosure mempty (makeConjunction asms `Implies` stmt))

unAsm :: Asm -> Formula
unAsm (Asm phi) = phi
unAsm (AsmStruct x sp) = TermSymbol Nowhere (SymbolPredicate (PredicateNounStruct sp)) [TermVar x]

buildBlocks :: [Block] -> TextBuilder
buildBlocks = \case
    BlockAxiom _pos lbl (Axiom asms stmt) : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Fact " <> buildMarker lbl <> text " : " <> buildFormula phi <> text ".\nAdmitted.\n" <> buildBlocks blocks
    BlockLemma _pos lbl (Lemma asms stmt) : BlockProof _ _ _ : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Theorem " <> buildMarker lbl <> text " : " <> buildFormula phi <> text ".\nAdmitted.\n" <> buildBlocks blocks
    BlockLemma _pos lbl (Lemma asms stmt) : blocks ->
        let phi = closure (unAsm <$> asms) stmt
        in text "Theorem " <> buildMarker lbl <> text " : " <> buildFormula phi <> text ".\nAdmitted.\n" <> buildBlocks blocks
    BlockDefn _pos _lbl defn : blocks->
        buildDefn defn <> buildBlocks blocks
    BlockAbbr _pos _lbl abbr : blocks->
        buildAbbr abbr <> buildBlocks blocks
    [] ->
        mempty
    block : _ ->
        _TODO ("builBlocks" <> show block)

buildDefn :: Defn -> TextBuilder
buildDefn = \case
    DefnPredicate [] predi xs phi ->
        "Definition " <> buildSymbol (SymbolPredicate predi) <> " := " <>
        "fun " <> buildVarSymbols xs <> ": set => " <> buildFormula phi <> ".\n"
    DefnFun [] f xs phi ->
        "Definition " <> buildSymbol (SymbolFun f) <> " := " <>
        buildSetFunIfNonEmpty (buildVarSymbols xs) (buildFormula phi) <> ".\n"
    DefnOp f xs phi ->
        "Definition " <> buildSymbol (SymbolMixfix f) <> " := " <>
        buildSetFunIfNonEmpty (buildVarSymbols xs) (buildFormula phi) <> ".\n"
    _ ->
        error "assumptions in definition, deprecated"

buildAbbr :: Abbreviation -> TextBuilder
buildAbbr (Abbreviation f body) =
    "Definition " <> buildSymbol f <> " := " <>
    buildSetFunIfNonEmpty buildBindings' (buildFormula ((instantiate (TermVar . FreshVar) (fmap absurd body)))) <> ".\n"
        where
            buildBindings' :: TextBuilder
            buildBindings' = intercalate (char ' ') (buildVarSymbol . FreshVar <$> List.sort (List.nub (bindings body)))

buildSetFunIfNonEmpty :: TextBuilder -> TextBuilder -> TextBuilder
buildSetFunIfNonEmpty xs b = if isEmpty xs then b else "fun " <> xs <> " : set => " <> b

buildFormula :: Formula -> TextBuilder
buildFormula = \case
    TermVar x -> buildVarSymbol x
    -- We handle eq in a special manner to avoid having to specify the type of the equality.
    TermSymbol _pos f [x,y] | isEqSymbol f ->
        char '(' <> buildFormula x <> text " = " <> buildFormula y <> char ')'
    TermSymbol _pos f [x,y] | isDiseqSymbol f ->
        char '(' <> buildFormula x <> text " <> " <> buildFormula y <> char ')'
    TermSymbol _pos f es ->
        let es' = buildSymbol f : (buildFormula <$> es)
        in char '(' <> intercalate (char ' ') es' <> char ')'
    Apply e es ->
        let es' = NonEmpty.cons (buildFormula e) (buildFormula <$> es)
        in char '(' <> intercalate (char ' ') es' <> char ')'
    Not _pos e -> text "~(" <> buildFormula e <> char ')'
    Connected conn e1 e2 ->
        char '(' <> buildConn conn (buildFormula e1) (buildFormula e2) <> char ')'
    Quantified quant body ->
        char  '(' <> buildQuant quant <> char ' ' <> buildBindings body <> text ",(" <> buildFormula (instantiate TermVar body) <> text "))"
    TermSep x bound phi ->
        char '{' <> buildVarSymbol x <> " :e (" <> buildFormula bound <> text ")|" <> buildFormula (instantiate1 (TermVar x) phi) <> char '}'
    ReplacePred y x xB body ->
        let x' = buildVarSymbol x
            y' = buildVarSymbol y
            fromReplacementVar = \case
                ReplacementDomVar -> TermVar x
                ReplacementRangeVar -> TermVar y
            body' = buildFormula (instantiate fromReplacementVar body)
        in "let MkReplFun := fun " <> x' <> " : set => (Eps_i (fun " <> y' <> "=>" <> body' <> ")) in {MkReplFun " <> x' <> "|" <> x' <> " :e (" <> buildFormula xB <> ")}"
    ReplaceFun ((x, xB) :| []) lhs cond ->
        let x' = buildVarSymbol x
            xB' = "(" <> buildFormula xB <> ")" -- parens probably not needed
            lhs' = "(fun " <> x' <> " => " <> buildFormula (instantiate TermVar lhs) <> ")"
            cond' = "(fun " <> x' <> " => " <> buildFormula (instantiate TermVar cond) <> ")"
        -- Using "ReplSep : set->(set->prop)->(set->set)->set"
        in "ReplSep " <> xB' <> cond' <> lhs'
    ReplaceFun ((x, xB) :| (y, yB) : []) lhs cond ->
        let x' = buildVarSymbol x
            xB' = "(" <> buildFormula xB <> ")"
            y' = buildVarSymbol y
            yB' = "(fun dummyVar => " <> buildFormula yB <> ")"
            lhs' = "(fun " <> x' <> " " <> y' <> " => " <> buildFormula (instantiate TermVar lhs) <> ")"
            cond' = "(fun " <> x' <> " " <> y' <> " => " <> buildFormula (instantiate TermVar cond) <> ")"
        -- Using "ReplSep2 : set -> (set -> set) -> (set -> set -> prop) -> (set -> set -> set) -> set"
        in "ReplSep2 " <> xB' <> yB' <> cond' <> lhs'
    ReplaceFun bounds lhs cond ->
        -- Silly placeholder translation for now
        let iff = makeReplacementIff (TermVar (F "frs")) bounds lhs cond
        in "Eps_i (fun frs : set => " <> buildFormula iff <> ")"
    Lambda _ -> text "TODO_buildFormula_Lambda"
    PropositionalConstant IsTop -> "True"
    PropositionalConstant IsBottom -> "False"
    TermSymbolStruct f me ->
        let f' = buildMarker (Marker (unStructSymbol f))
            e = me ?? error "unannotated struct op"
        in char '(' <> f' <> buildFormula e <> char ')'

buildMarker :: Marker -> TextBuilder
buildMarker (Marker m)= text m

buildQuant :: Quantifier -> TextBuilder
buildQuant = \case
    Universally -> "forall"
    Existentially -> "exists"

buildBindings :: Scope VarSymbol ExprOf a -> TextBuilder
buildBindings body = intercalate (char ' ') (buildVarSymbol <$> List.nub (bindings body))

buildBounds :: NonEmpty (VarSymbol, ExprOf VarSymbol) -> TextBuilder
buildBounds (bound :| bounds) = foldr (\b bs -> buildBound b <> "/\\ " <> bs) (buildBound bound) bounds
    where
        buildBound (y, yB) = buildVarSymbol y <> " :e (" <> buildFormula yB <> ")"

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

buildSymbol :: Symbol -> TextBuilder
buildSymbol (SymbolInteger i) = decimal i
buildSymbol symb = fromRightMarker case symb of
    SymbolMixfix f ->
        Right (mixfixMarker f)
    SymbolFun f -> Right (lexicalItemSgPlMarker f)
    SymbolPredicate (PredicateAdj f) -> Right (lexicalItemMarker f)
    SymbolPredicate (PredicateVerb f) -> Right (lexicalItemSgPlMarker f)
    SymbolPredicate (PredicateNoun f) -> Right (lexicalItemSgPlMarker f)
    SymbolPredicate (PredicateRelation f) -> Right (relationSymbolMarker f)
    SymbolPredicate (PredicateNounStruct f) -> Right (lexicalItemSgPlMarker f)
    SymbolPredicate (PredicateSymbol f) -> Right (Marker f) -- HM.lookup f (lexiconPrefixPredicates lexi)


fromRightMarker :: Either String Marker -> TextBuilder
fromRightMarker = \case
    Right (Marker m) -> text m
    Left a -> error ("symbol not in lexicon" <> a)

isEqSymbol :: Symbol -> Bool
isEqSymbol = \case
    SymbolPredicate (PredicateRelation EqSymbol) -> True
    SymbolPredicate (PredicateVerb f) | f == mkLexicalItemSgPl (unsafeReadPhraseSgPl "equal[s/] ?") "eq" -> True
    SymbolPredicate (PredicateAdj f) | f == mkLexicalItem (unsafeReadPhrase "equal to ?") "eq" -> True
    _ -> False

isDiseqSymbol :: Symbol -> Bool
isDiseqSymbol = \case
    SymbolPredicate (PredicateRelation NeqSymbol) -> True
    SymbolPredicate (PredicateAdj f) | f == mkLexicalItem (unsafeReadPhrase "distinct from ?") "neq" -> True
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
