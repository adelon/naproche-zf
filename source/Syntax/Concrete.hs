{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

-- | Concrete syntax of the surface language.
module Syntax.Concrete where

import Base
import Syntax.Abstract
import Syntax.Concrete.Keywords
import Syntax.Lexicon (Lexicon(..), lexiconAdjs, splitOnVariableSlot)
import Syntax.Token

import Data.HashSet qualified as HS
import Data.List.NonEmpty qualified as NonEmpty
import Data.HashMap.Strict qualified as HM
import Text.Earley (Grammar, Prod, (<?>), rule, satisfy, terminal)
import Text.Earley.Mixfix
import Text.Megaparsec.Pos (SourcePos)


grammar :: Lexicon -> Grammar r (Prod r Text (Located Token) Block)
grammar lexicon@Lexicon{..} = mdo
    let makeOp :: ([Maybe Token], Associativity) -> ([Maybe (Prod r Text (Located Token) Token)], Associativity)
        makeOp (pat, assoc) = (map (fmap token) pat, assoc)
        ops = map (map makeOp) (toList (HM.toList . HM.map fst <$> lexiconMixfix))
        conns = map (map makeOp) lexiconConnectives

    integer    <- rule (terminal maybeIntToken <?> "integer")
    relator    <- rule $ unLocated <$> (satisfy (\ltok -> unLocated ltok `HM.member` lexiconRelationSymbols) <?> "relator")
    varSymbol  <- rule (terminal maybeVarToken <?> "variable")
    varSymbols <- rule (commaList varSymbol)
    cmd        <- rule (terminal maybeCmdToken <?> "TEX command")
--
-- Formulas have three levels:
--
-- + Expressions: atoms or operators applied to atoms.
-- + Chains:      comma-lists of expressions, separated by relators.
-- + Formulas:    chains or connectives applied to chains.
--
-- For example, the formula @x, y < z \implies x, y < z + 1@ consist of the
-- connective @\implies@ applied to two chains @x, y < z@ and @x, y < z + 1@.
-- In turn, the chain @x, y < z + 1@ consist of three expressions,
-- @x@, @y@, and @z + 1@. Finally, @z + 1@ consist the operator @+@
-- applied to two atoms, the variable @z@ and the number literal @1@.
--
-- This split is due to the different behaviour of relators compared to
-- operators and connectives. Relators can chain (@x < y < z@) and allow
-- lists as arguments, as in the above example. Operators and connectives
-- instead have precedence and fixity. The only syntactic difference between
-- an operator and a connective is the relative precedence compared to relators.
--
    replaceBound  <- rule $ (,) <$> varSymbol <* _in <*> expr
    replaceBounds <- rule $ commaList replaceBound
    replaceFun    <- rule $ ExprReplace <$> expr <* _pipe <*> replaceBounds <*> optional (_pipe *> comprStmt)
    comprStmt   <- rule $ (StmtFormula <$> formula) <|> text stmt

    replacePredSymbolic <- rule $ ExprReplacePred <$> varSymbol <* _pipe <*> (command "exists" *> varSymbol) <* _in <*> expr <* _dot <*> (StmtFormula <$> formula)
    replacePredText     <- rule $ ExprReplacePred <$> varSymbol <* _pipe <*> (begin "text" *> _exists *> beginMath *> varSymbol <* _in) <*> expr <* endMath <* _suchThat <*> stmt <* end "text"
    replacePred         <- rule $ replacePredSymbolic <|> replacePredText

    let exprStructOpOf ann = HS.foldr alg empty (HM.keysSet lexiconStructFun)
            where
                alg s prod = prod <|> (ExprStructOp <$> structSymbol s <*> ann)

    exprStructOp <- rule (exprStructOpOf (optional (bracket expr)))

    let bracedArgs1 ar arg = count1 ar $ group arg
    let prefixPredicateOf f arg symb@(PrefixPredicate c ar) = f <$> pure symb <* command c <*> bracedArgs1 ar arg


    exprParen   <- rule $ paren expr
    exprInteger <- rule $ ExprInteger <$> integer
    exprVar     <- rule $ ExprVar <$> varSymbol
    exprTuple   <- rule $ makeTuple <$> paren (commaList2 expr)
    exprSep     <- rule $ brace $ ExprSep <$> varSymbol <* _in <*> expr <* _pipe <*> comprStmt
    exprReplace <- rule $ brace $ (replaceFun <|> replacePred)
    exprFinSet  <- rule $ brace $ ExprFiniteSet <$> exprs
    exprBase    <- rule $ asum [exprVar, exprInteger, exprStructOp, exprParen, exprTuple, exprSep, exprReplace, exprFinSet]
    exprApp     <- rule $ ExprApp <$> exprBase <*> (paren expr <|> exprTuple)
    expr        <- mixfixExpression ops (exprBase <|> exprApp) ExprOp
    exprs       <- rule $ commaList expr

    relationSign   <- rule $ pure Positive <|> (Negative <$ command "not")
    relationExpr   <- rule $ RelationExpr <$> (command "mathrel" *> group expr)
    relation       <- rule $ (RelationSymbol <$> relator) <|> relationExpr
    chainBase      <- rule $ ChainBase <$> exprs <*> relationSign <*> relation <*> exprs
    chainCons      <- rule $ ChainCons <$> exprs <*> relationSign <*> relation <*> chain
    chain          <- rule $ chainCons <|> chainBase

    formulaPredicate  <- rule $ asum $ prefixPredicateOf FormulaPredicate expr <$> HM.keys lexiconPrefixPredicates
    formulaChain      <- rule $ FormulaChain <$> chain
    formulaBottom     <- rule $ PropositionalConstant IsBottom <$ command "bot" <?> "\"\\bot\""
    formulaTop        <- rule $ PropositionalConstant IsTop    <$ command "top" <?> "\"\\top\""
    formulaExists     <- rule $ FormulaQuantified Existentially <$> (command "exists" *> varSymbols) <*> maybeBounded <* _dot <*> formula
    formulaAll        <- rule $ FormulaQuantified Universally  <$> (command "forall" *> varSymbols) <*> maybeBounded <* _dot <*> formula
    formulaQuantified <- rule $ formulaExists <|> formulaAll
    formulaBase       <- rule $ asum [formulaChain, formulaPredicate, formulaBottom, formulaTop, paren formula]
    formulaConn       <- mixfixExpression conns formulaBase makeConnective
    formula           <- rule $ formulaQuantified <|> formulaConn

-- These are asymmetric formulas (only variables are allowed on one side).
-- They express judgements.
--
    assignment  <- rule $ (,) <$> varSymbol <* (_eq <|> _defeq) <*> expr
    typing      <- rule $ (,) <$> varSymbols <* (_in <|> _colon) <*> expr

    adjL     <- rule $ adjLOf lexicon term
    adjR     <- rule $ adjROf lexicon term
    adj      <- rule $ adjOf lexicon term
    adjVar   <- rule $ adjOf lexicon var

    var  <- rule $ math varSymbol
    vars <- rule $ math varSymbols

    verb     <- rule $ verbOf lexicon sg term
    verbPl   <- rule $ verbOf lexicon pl term
    verbVar  <- rule $ verbOf lexicon sg var

    noun      <- rule $ nounOf lexicon sg term nounName -- Noun with optional variable name.
    nounList  <- rule $ nounOf lexicon sg term nounNames -- Noun with a list of names.
    nounVar   <- rule $ fst <$> nounOf lexicon sg var (pure Nameless) -- No names in defined nouns.
    nounPl    <- rule $ nounOf lexicon pl term nounNames
    nounPlMay <- rule $ nounOf lexicon pl term nounName


    structNoun <- rule $ structNounOf lexicon sg var var
    structNounNameless <- rule $ fst <$> structNounOf lexicon sg var (pure Nameless)


    fun      <- rule $ funOf lexicon sg term
    funVar   <- rule $ funOf lexicon sg var

    attrRThat   <- rule $ AttrRThat <$> thatVerbPhrase
    attrRThats  <- rule $ ((:[]) <$> attrRThat) <|> ((\a a' -> [a,a']) <$> attrRThat <* _and <*> attrRThat) <|> pure []
    attrRs      <- rule $ ((:[]) <$> adjR)      <|> ((\a a' -> [a,a']) <$> adjR <* _and <*> adjR)           <|> pure []
    attrRight   <- rule $ (<>) <$> attrRs <*> attrRThats

    verbPhraseVerbSg    <- rule $ VPVerb <$> verb
    verbPhraseVerbNotSg <- rule $ VPVerbNot <$> (_does *> _not *> verbPl)
    verbPhraseAdjSg     <- rule $ VPAdj . (:|[]) <$> (_is *> adj)
    verbPhraseAdjAnd    <- rule do {_is; a1 <- adj; _and; a2 <- adj; pure (VPAdj (a1 :| [a2]))}
    verbPhraseAdjNotSg  <- rule $ VPAdjNot . (:|[]) <$> (_is *> _not *> adj)
    verbPhraseNotSg     <- rule $ verbPhraseVerbNotSg <|> verbPhraseAdjNotSg
    verbPhraseSg        <- rule $ verbPhraseVerbSg <|> verbPhraseAdjSg <|> verbPhraseAdjAnd <|> verbPhraseNotSg

    -- LATER can cause technical ambiguities? verbPhraseVerbPl    <- rule $ VPVerb <$> verbPl
    verbPhraseVerbNotPl <- rule $ VPVerbNot <$> (_do *> _not *> verbPl)
    verbPhraseAdjPl     <- rule $ VPAdj . (:|[]) <$> (_are *> adj)
    verbPhraseAdjNotPl  <- rule $ VPAdjNot . (:|[]) <$> (_are *> _not *> adj)
    verbPhraseNotPl     <- rule $ verbPhraseVerbNotPl <|> verbPhraseAdjNotPl
    verbPhrasePl        <- rule $ verbPhraseAdjPl <|> verbPhraseNotPl -- LATER <|> verbPhraseVerbPl



    thatVerbPhrase    <- rule $ _that *> verbPhraseSg

    nounName        <- rule $ optional (math varSymbol)
    nounNames       <- rule $ math (commaList_ varSymbol) <|> pure []
    nounPhrase      <- rule $ makeNounPhrase <$> many adjL <*> noun  <*> attrRight <*> optional suchStmt
    nounPhrase'     <- rule $ makeNounPhrase <$> many adjL <*> nounList <*> attrRight <*> optional suchStmt
    nounPhrasePl    <- rule $ makeNounPhrase <$> many adjL <*> nounPl <*> attrRight <*> optional suchStmt
    nounPhrasePlMay <- rule $ makeNounPhrase <$> many adjL <*> nounPlMay <*> attrRight <*> optional suchStmt
    nounPhraseMay   <- rule $ makeNounPhrase <$> many adjL <*> noun <*> attrRight <*> optional suchStmt

    -- Quantification phrases for quantification and indfinite terms.
    quantAll   <- rule $ QuantPhrase Universally <$> (_forEvery *> nounPhrase' <|> _forAll *> nounPhrasePl)
    quantSome  <- rule $ QuantPhrase Existentially <$> (_some *> (nounPhrase' <|> nounPhrasePl))
    quantNone  <- rule $ QuantPhrase Nonexistentially <$> (_no *> (nounPhrase' <|> nounPhrasePl))
    quant      <- rule $ quantAll <|> quantSome <|> quantNone -- <|> quantUniq


    termExpr       <- rule $ TermExpr <$> math expr
    termFun        <- rule $ TermFun <$> (optional _the *> fun)
    termIota       <- rule $ TermIota <$> (_the *> var) <* _suchThat <*> stmt
    termAll        <- rule $ TermQuantified Universally <$> (_every *> nounPhraseMay)
    termSome       <- rule $ TermQuantified Existentially <$> (_some *> nounPhraseMay)
    termNo         <- rule $ TermQuantified Nonexistentially <$> (_no *> nounPhraseMay)
    termQuantified <- rule $ termAll <|> termSome <|> termNo
    term           <- rule $ termExpr <|> termFun <|> termQuantified <|> termIota

-- Basic statements @stmt'@ are statements without any conjunctions or quantifiers.
--
    let singletonTerm = (:| []) <$> term
        nonemptyTerms = andList1 term
    stmtVerbSg    <- rule $ StmtVerbPhrase <$> singletonTerm <*> verbPhraseSg
    stmtVerbPl    <-rule $ StmtVerbPhrase <$> andList1 term <*> verbPhrasePl
    stmtVerb      <- rule $ stmtVerbSg <|> stmtVerbPl
    stmtNounIs    <- rule $ StmtNoun <$> singletonTerm <* _is <* _an <*> nounPhrase
    stmtNounAre   <- rule $ StmtNoun <$> (nonemptyTerms <* _are) <*> nounPhrasePlMay
    stmtNounIsNot <- rule $ StmtNeg <$> (StmtNoun <$> singletonTerm <* _is <* _not <* _an <*> nounPhrase)
    stmtNounAreNot <- rule $ StmtNeg <$> (StmtNoun <$> nonemptyTerms <* (_are *> _not) <*> nounPhrasePlMay)
    stmtNoun      <- rule $ stmtNounIs <|> stmtNounIsNot <|> stmtNounAre <|> stmtNounAreNot
    stmtStruct    <- rule $ StmtStruct <$> (term <* _is <* _an) <*> structNounNameless
    stmtExists    <- rule $ StmtExists <$> (_exists *> _an *> nounPhrase')
    stmtExist     <- rule $ StmtExists <$> (_exist *> nounPhrasePl)
    stmtExistsNot <- rule $ StmtNeg . StmtExists <$> (_exists *> _no *> nounPhrase')
    stmtFormula   <- rule $ StmtFormula <$> math formula
    stmtFormualNeg <- rule $ StmtNeg . StmtFormula <$> (_not *> math formula)
    stmtBot       <- rule $ StmtFormula (PropositionalConstant IsBottom) <$ _contradiction
    stmt'         <- rule $ stmtVerb <|> stmtNoun <|> stmtStruct <|> stmtFormula <|> stmtFormualNeg <|> stmtBot
    stmtOr  <- rule $ stmt'   <|> (StmtConnected Disjunction <$> stmt'   <* _or  <*> stmt)
    stmtAnd <- rule $ stmtOr  <|> (StmtConnected Conjunction <$> stmtOr  <* _and <*> stmt)
    stmtIff <- rule $ stmtAnd <|> (StmtConnected Equivalence <$> stmtAnd <* _iff <*> stmt)
    stmtIf  <- rule $ StmtConnected Implication <$> (_if *> stmt) <* optional _comma <* _then <*> stmt
    stmtXor <- rule $ StmtConnected ExclusiveOr <$> (_either *> stmt) <* _or <*> stmt
    stmtNor <- rule $ StmtConnected NegatedDisjunction <$> (_neither *> stmt) <* _nor <*> stmt
    stmtNeg <- rule $ StmtNeg <$> (_itIsWrong *> stmt)

    stmtQuantPhrase <- rule $ StmtQuantPhrase <$> (_for *> quant) <* optional _comma <* optional _have <*> stmt

    suchStmt <- rule $ _suchThat *> stmt <* optional _comma


   -- Symbolic quantifications with or without generalized bounds.
    symbolicForall <- rule $ SymbolicForall
        <$> ((_forAll <|> _forEvery) *> beginMath *> varSymbols)
        <*> maybeBounded <* endMath
        <*> optional suchStmt
        <* optional _have <*> stmt
    symbolicExists <- rule $ SymbolicExists
        <$> ((_exists <|> _exist) *> beginMath *> varSymbols)
        <*> maybeBounded <* endMath
        <*> ((_suchThat *> stmt) <|> pure (StmtFormula (PropositionalConstant IsTop)))
    symbolicNotExists <- rule $ SymbolicNotExists
        <$> (_exists *> _no *> beginMath *> varSymbols)
        <*> maybeBounded <* endMath
        <* _suchThat <*> stmt
    symbolicBound <- rule $ Bounded <$> relationSign <*> relation <*> expr
    maybeBounded <- rule (pure Unbounded <|> symbolicBound)

    symbolicQuantified <- rule $ symbolicForall <|> symbolicExists <|> symbolicNotExists

    stmt <- rule $ asum [stmtNeg, stmtIf, stmtXor, stmtNor, stmtExists, stmtExist, stmtExistsNot, stmtQuantPhrase, stmtIff, symbolicQuantified] <?> "a statement"

    asmLetIn        <- rule $ uncurry AsmLetIn <$> (_let *> math typing)
    asmLetNoun      <- rule $ AsmLetNoun <$> (_let *> fmap pure var <* (_be <|> _denote) <* _an) <*> nounPhrase
    asmLetNouns     <- rule $ AsmLetNoun <$> (_let *> vars <* (_be <|> _denote)) <*> nounPhrasePlMay
    asmLetEq        <- rule $ uncurry AsmLetEq <$> (_let *> math assignment)
    asmLetThe       <- rule $ AsmLetThe <$> (_let *> var <* _be <* _the) <*> fun
    asmLetStruct    <- rule $ AsmLetStruct <$> (_let *> var <* _be <* _an) <*> structNounNameless
    asmLet          <- rule $ asmLetNoun <|> asmLetNouns <|> asmLetIn <|> asmLetEq <|> asmLetThe <|> asmLetStruct
    asmSuppose      <- rule $ AsmSuppose <$> (_suppose *> stmt)
    asm             <- rule $ andList1_ (asmLet <|> asmSuppose) <* _dot
    asms            <- rule $ concat <$> many asm

    axiom <- rule $ Axiom <$> asms <* optional _then <*> stmt <* _dot

    lemma <- rule $ Lemma <$> asms <* optional _then <*> stmt <* _dot

    defnAdj <- rule $ DefnAdj <$> optional (_an *> nounPhrase) <*> var <* _is <*> adjVar
    defnVerb <- rule $ DefnVerb <$> optional (_an *> nounPhrase) <*> var <*> verbVar
    defnNoun <- rule $ DefnNoun <$> var <* _is <* _an <*> nounVar
    defnRel <- rule $ DefnRel <$> (beginMath *> varSymbol) <*> relator <*> varSymbol <* endMath
    defnSymbolicPredicate <- rule $ math $ asum $ prefixPredicateOf DefnSymbolicPredicate varSymbol <$> HM.keys lexiconPrefixPredicates
    defnHead <- rule $ optional _write *> asum [defnAdj, defnVerb, defnNoun, defnRel, defnSymbolicPredicate]

    defnIf <- rule $ Defn <$> asms <*> defnHead <* (_iff <|> _if) <*> stmt <* _dot
    defnFunSymb <- rule $ _comma *> termExpr <* _comma --  ^ Optional symbolic equivalent.
    defnFun <- rule $ DefnFun <$> asms <*> (optional _the *> funVar) <*> optional defnFunSymb <* _is <*> term <* _dot

    symbolicPatternEqTerm <- rule do
        pat <- beginMath *> symbolicPattern <* _eq
        e <- expr <* endMath <* _dot
        pure (pat, e)
    defnOp <- rule $ uncurry DefnOp <$> symbolicPatternEqTerm

    defn <- rule $ defnIf <|> defnFun <|> defnOp

    abbreviationVerb  <- rule $ AbbreviationVerb <$> var <*> verbVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationAdj   <- rule $ AbbreviationAdj <$> var <* _is <*> adjVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationNoun  <- rule $ AbbreviationNoun <$>  var <* _is <* _an <*> nounVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationRel   <- rule $ AbbreviationRel <$> (beginMath *> varSymbol) <*> relator <*> varSymbol <* endMath <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationFun   <- rule $ AbbreviationFun <$> (_the *> funVar) <* (_is <|> _denotes) <*> term <* _dot
    abbreviationEq    <- rule $ uncurry AbbreviationEq <$> symbolicPatternEqTerm
    abbreviation      <- rule $ (abbreviationVerb <|> abbreviationAdj <|> abbreviationNoun <|> abbreviationRel <|> abbreviationFun <|> abbreviationEq)

    datatypeFin <- rule $ DatatypeFin <$> fmap fst (_an *> noun) <*> (_is *> _oneOf *> orList2 (math cmd) <* _dot)
    datatype    <- rule datatypeFin

    unconditionalIntro <- rule $ IntroRule [] <$> math formula
    conditionalIntro   <- rule $ IntroRule <$> (_if *> andList1_ (math formula)) <* _comma <* _then <*> math formula
    inductiveIntro     <- rule $ (unconditionalIntro <|> conditionalIntro) <* _dot
    inductiveDomain    <- rule $ math $ (,) <$> symbolicPattern <* _subseteq <*> expr
    inductiveHead      <- rule $ _define *> inductiveDomain <* optional _inductively <* optional _asFollows <* _dot
    inductive          <- rule $ uncurry Inductive <$> inductiveHead <*> enumerated1 inductiveIntro

    signatureAdj      <- rule $ SignatureAdj <$> var <* _can <* _be <*> adjOf lexicon var
    symbolicPattern   <- symbolicPatternOf ops varSymbol
    signatureSymbolic <- rule $ SignatureSymbolic <$> math symbolicPattern <* _is <* _an <*> nounPhrase
    signature         <- rule $ (,) <$> asms <* optional _then <*> (signatureAdj <|> signatureSymbolic) <* _dot

    structFix <- rule do
        beginMath
        rawCmd <- cmd
        endMath
        pure (StructSymbol rawCmd)
    structDefn <- rule $ do
        _an
        ~(structPhrase, structLabel) <- structNoun
        _extends
        structParents <- andList1_ (_an *> structNounNameless)
        maybeFixes <- optional (_equipped *> enumerated structFix)
        structAssumes <- (_suchThat *> enumeratedMarked (stmt <* _dot)) <|> ([] <$ _dot)
        pure StructDefn
            { structPhrase = structPhrase
            , structLabel = structLabel
            , structParents = structParents
            , structFixes = maybeFixes ?? []
            , structAssumes = structAssumes
            }

    justificationSet <- rule $ JustificationSetExt <$ _bySetExt
    justificationRef <- rule $ JustificationRef <$> (_by *> ref)
    justificationLocal <- rule $ JustificationLocal <$ (_by *> (_assumption <|> _definition))
    justification <- rule (justificationSet <|> justificationRef <|> justificationLocal <|> pure JustificationEmpty)

    trivial          <- rule $ Qed JustificationEmpty <$ _trivial <* _dot
    omitted          <- rule $ Omitted <$ _omitted <* _dot
    qedJustified     <- rule $ Qed <$> (_follows *> justification <* _dot)
    qed              <- rule $ qedJustified <|> trivial <|> omitted <|> pure (Qed JustificationEmpty)

    let alignedEq = symbol "&=" <?> "\"&=\""
    explanation <- rule $ (text justification) <|> pure JustificationEmpty
    equationItem <- rule $ (,) <$> (alignedEq *> expr) <*> explanation
    equations <- rule $ Equation <$> expr <*> (many1 equationItem)

    let alignedIff = symbol "&" *> command "iff" <?> "\"&\\iff\""
    biconditionalItem <- rule $ (,) <$> (alignedIff *> formula) <*> explanation
    biconditionals <- rule $ Biconditionals <$> formula <*> (many1 biconditionalItem)

    calc  <- rule $ Calc <$> align (equations <|> biconditionals) <*> proof

    caseOf           <- rule $ command "caseOf" *> token InvisibleBraceL *> stmt <* _dot <* token InvisibleBraceR
    byCases          <- rule $ ByCase <$> env_ "byCase" (many1_ (Case <$> caseOf <*> proof))
    byContradiction  <- rule $ ByContradiction <$ _suppose <* _not <* _dot <*> proof
    bySetInduction   <- rule $ BySetInduction <$> proofBy (_in *> word "-induction" *> optional (word "on" *> term)) <*> proof
    byOrdInduction   <- rule $ ByOrdInduction <$> proofBy (word "transfinite" *> word "induction" *> proof)
    assume           <- rule $ Assume <$> (_suppose *> stmt <* _dot) <*> proof

    fixSymbolic      <- rule $ FixSymbolic <$> (_fix *> beginMath *> varSymbols) <*> maybeBounded <* endMath <* _dot <*> proof
    fixSuchThat      <- rule $ FixSuchThat <$> (_fix *> math varSymbols) <* _suchThat <*> stmt <* _dot <*> proof
    fix              <- rule $ fixSymbolic <|> fixSuchThat

    takeVar          <- rule $ TakeVar <$> (_take *> beginMath *> varSymbols) <*> maybeBounded <* endMath <* _suchThat <*> stmt <*> justification <* _dot <*> proof
    takeNoun         <- rule $ TakeNoun <$> (_take *> _an *> (nounPhrase' <|> nounPhrasePl)) <*> justification <* _dot <*> proof
    take             <- rule $ takeVar <|> takeNoun
    suffices         <- rule $ Suffices <$> (_sufficesThat *> stmt) <*> (justification <* _dot) <*> proof
    subclaim         <- rule $ Subclaim <$> (_show *> stmt <* _dot) <*> env_ "subproof" proof <*> proof
    have             <- rule $ Have <$> optional (_since *> stmt <* _comma <* _have) <* optional _haveIntro <*> stmt <*> justification <* _dot <*> proof

    define           <- rule $ Define <$> (_let *> beginMath *> varSymbol <* _eq) <*> expr <* endMath <* _dot <*> proof
    defineFunction   <- rule $ DefineFunction <$> (_let *> beginMath *> varSymbol) <*> paren varSymbol <* _eq <*>  expr <* endMath <* _for <* beginMath <*> varSymbol <* _in <*> expr <* endMath <* _dot <*> proof
    





    -- Define $f $\fromTo{X}{Y} such that,         
    -- Define function $f: X \to Y$,
    -- \begin{align}
    --      &x \mapsto 3*x      &,  
    --      &x \mapsto 4*k    &,    \forall k \in \N. x \in \Set{k}
    -- \end{align}
    -- 

    -- Follwing is the definition right now.
    -- Define function $f: X \to Y$ such that,
    -- \begin{cases}
    --     1 & \text{if } x \in \mathbb{Q}\\
    --     0 & \text{if } x \in \mathbb{R}\setminus\mathbb{Q}
    --     3 & \text{else}     
    -- \end{cases}

    functionDefineCase <- rule $ (:[]) <$> ((,) <$> expr <*> (_ampersand *> formula))
    defineFunctionMathy <-  rule    $ DefineFunctionMathy 
                                    <$> (_define *> beginMath *> varSymbol)           -- Define $ f
                                    <*> (_colon *> varSymbol)                           -- : 'var' \to 'var'
                                    <*> (_to *> varSymbol <* endMath <* _suchThat) 
                                    -- <*> (_suchThat  *> align (many1 ((_ampersand *> varSymbol <* _mapsto) <*> exprApp <*> (_ampersand *> formula))))
                                    -- <*> (_suchThat  *> align (many1 (varSymbol <* exprApp <*  formula)))
                                    <*> varSymbol <*> varSymbol <* symbol "="
                                    <*> many1 functionDefineCase
                                    <*> proof 



    proof            <- rule $ asum [byContradiction, byCases, bySetInduction, byOrdInduction, calc, subclaim, assume, fix, take, have, suffices, define, defineFunction, defineFunctionMathy, qed]


    blockAxiom  <- rule $ uncurry3 BlockAxiom     <$> envPos  "axiom" axiom
    blockLemma  <- rule $ uncurry3 BlockLemma     <$> lemmaEnv lemma
    blockProof  <- rule $ uncurry  BlockProof     <$> envPos_ "proof" proof
    blockDefn   <- rule $ uncurry3 BlockDefn      <$> envPos "definition" defn
    blockAbbr   <- rule $ uncurry3 BlockAbbr      <$> envPos "abbreviation" abbreviation
    blockData   <- rule $ uncurry  BlockData      <$> envPos_ "datatype" datatype
    blockInd    <- rule $ uncurry3 BlockInductive <$> envPos "inductive" inductive
    blockSig    <- rule $ (\(p, (a, s)) -> BlockSig p a s) <$> envPos_ "signature" signature
    blockStruct <- rule $ uncurry3 BlockStruct    <$> envPos "struct" structDefn
    block       <- rule $ asum [blockAxiom, blockLemma, blockDefn, blockAbbr, blockData, blockInd, blockSig, blockStruct, blockProof]

    -- Starting category.
    pure block


proofBy :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
proofBy method = bracket $ word "proof" *> word "by" *> method


lemmaEnv :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (SourcePos, Marker, a)
lemmaEnv content = asum
    [ envPos "theorem" content
    , envPos "lemma" content
    , envPos "corollary" content
    , envPos "claim" content
    , envPos "proposition" content
    ]


-- | A disjunctive list with at least two items:
-- * 'a or b'
-- * 'a, b, or c'
-- * 'a, b, c, or d'
--
orList2 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
orList2 item = ((:|) <$> item <*> many (_commaOr *> item))
    <|> ((\i j -> i:|[j]) <$> item <* _or <*> item)


-- | Nonempty textual lists of the form "a, b, c, and d".
-- The final comma is mandatory, 'and' is not.
-- Also allows "a and b". Should therefore be avoided in contexts where
-- a logical conjunction would also be possible.
-- Currently also allows additional 'and's after each comma...
--
andList1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
andList1 item = ((:|) <$> item <*> many (_commaAnd *> item))
    <|> ((\i j -> i:|[j]) <$> item <* _and <*> item)

-- | Like 'andList1', but drops the information about nonemptiness.
andList1_ :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [a]
andList1_ item = NonEmpty.toList <$> andList1 item


commaList :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
commaList item = (:|) <$> item <*> many (_comma *> item)

-- | Like 'commaList', but drops the information about nonemptiness.
commaList_ :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [a]
commaList_ item = NonEmpty.toList <$> commaList item

-- | Like 'commaList', but requires at least two items (and hence at least one comma).
commaList2 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
commaList2 item = (:|) <$> item <* _comma <*> commaList_ item


enumerated :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [a]
enumerated p = NonEmpty.toList <$> enumerated1 p

enumerated1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
enumerated1 p = begin "enumerate" *> many1 (command "item" *> p) <* end "enumerate" <?> "\"\\begin{enumerate} ...\""


enumeratedMarked :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [(Marker, a)]
enumeratedMarked p = NonEmpty.toList <$> enumeratedMarked1 p

enumeratedMarked1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty (Marker, a))
enumeratedMarked1 p = begin "enumerate" *> many1 ((,) <$> (command "item" *> label) <*> p) <* end "enumerate" <?> "\"\\begin{enumerate}\\item\\label{...}...\""



-- This function could be rewritten, so that it can be used directly in the grammar,
-- instead of with specialized variants.
--
phraseOf
    :: (pat -> [a] -> b)
    -> Lexicon
    -> (Lexicon -> HashSet pat)
    -> (pat -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) b
phraseOf constr lexicon selector proj arg =
    uncurry constr <$> asum (fmap make pats)
    where
        pats = HS.toList (selector lexicon)
        make pat = (\args -> (pat, args)) <$> go (proj pat)
        go = \case
            Just w : ws  -> token w *> go ws
            Nothing : ws -> (:) <$> arg <*> go ws
            []           -> pure []

adjLOf :: Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjLOf arg)
adjLOf lexicon arg = phraseOf AdjL lexicon (HM.keysSet . lexiconAdjLs) id arg <?> "a left adjective"

adjROf :: Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjROf arg)
adjROf lexicon arg = phraseOf AdjR lexicon (HM.keysSet . lexiconAdjRs) id arg <?> "a right adjective"

adjOf :: Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjOf arg)
adjOf lexicon arg = phraseOf Adj lexicon (HM.keysSet . lexiconAdjs) id arg <?> "an adjective"

verbOf
    :: Lexicon
    -> (SgPl LexicalPhrase -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) (VerbOf a)
verbOf lexicon proj arg = phraseOf Verb lexicon (HM.keysSet . lexiconVerbs) proj arg

funOf
    :: Lexicon
    -> (SgPl LexicalPhrase -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) (FunOf a)
funOf lexicon proj arg = phraseOf Fun lexicon (HM.keysSet . lexiconFuns) proj arg <?> "functional phrase"


-- | A noun with a @t VarSymbol@ as name(s).
nounOf
    :: Lexicon
    -> (SgPl LexicalPhrase -> LexicalPhrase)
    -> Prod r Text (Located Token) arg
    -> Prod r Text (Located Token) (t VarSymbol)
    -> Prod r Text (Located Token) (NounOf arg, t VarSymbol)
nounOf lexicon proj arg vars =
    (\(args1, xs, args2, pat) -> (Noun pat (args1 <> args2), xs)) <$> asum (fmap make pats) <?>  "a noun"
    where
        pats = HM.keys (lexiconNouns lexicon)
        make pat =
            let (pat1, pat2) = splitOnVariableSlot (proj pat)
            in  (\args1 xs args2 -> (args1, xs, args2, pat)) <$> go pat1 <*> vars <*> go pat2
        go = \case
            Just w : ws  -> token w *> go ws
            Nothing : ws -> (:) <$> arg <*> go ws
            []           -> pure []

structNounOf
    :: Lexicon
    -> (SgPl LexicalPhrase -> LexicalPhrase)
    -> Prod r Text (Located Token) arg
    -> Prod r Text (Located Token) name
    -> Prod r Text (Located Token) (StructPhrase, name)
structNounOf lexicon proj arg name =
    (\(_args1, xs, _args2, pat) -> (pat, xs)) <$> asum (fmap make pats) <?> "a structure noun"
    where
        pats = HM.keys (lexiconStructNouns lexicon)
        make pat =
            let (pat1, pat2) = splitOnVariableSlot (proj pat)
            in  (\args1 xs args2 -> (args1, xs, args2, pat)) <$> go pat1 <*> name <*> go pat2
        go = \case
            Just w : ws  -> token w *> go ws
            Nothing : ws -> (:) <$> arg <*> go ws
            []           -> pure []


symbolicPatternOf
    :: forall r. [[(Holey (Prod r Text (Located Token) Token), Associativity)]]
    -> Prod r Text (Located Token) VarSymbol
    -> Grammar r (Prod r Text (Located Token) SymbolPattern)
symbolicPatternOf ops varSymbol = rule $ asum
    [ go op
    | ops' <- ops
    , (op, _assoc) <- ops'
    ] <?> "a symbolic pattern"
    where
        go :: Holey (Prod r Text (Located Token) Token) -> Prod r Text (Located Token) SymbolPattern
        go [] = pure $ SymbolPattern [] []
        go (head : tail) = case head of
            Just symb -> (\s (SymbolPattern op vs) -> SymbolPattern (Just s : op) vs) <$> symb <*> go tail
            Nothing -> (\v (SymbolPattern op vs) -> SymbolPattern (Nothing : op) (v : vs)) <$> varSymbol <*> go tail


makeNounPhrase
    :: [AdjL]
    -> (Noun, t VarSymbol)
    -> [AdjR]
    -> Maybe Stmt
    -> NounPhrase t
makeNounPhrase ls (n, vs) rs ms = NounPhrase ls n vs rs ms




begin, end :: Text -> Prod r Text (Located Token) SourcePos
begin kind = tokenPos (BeginEnv kind) <?> ("\"\\begin{" <> kind <> "}\"")
end kind   = tokenPos (EndEnv kind) <?> ("\"\\end{" <> kind <> "}\"")

-- | Surround a production rule @body@ with an environment of a certain @kind@ requiring a marker specified in a @\\label@.
-- Ignores the optional title after the beginning of the environment.
envPos :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) (SourcePos, Marker, a)
envPos kind body = do
    p <- begin kind <?> ("start of a \"" <> kind <> "\" environment")
    optional title
    m <- label
    a <- body <* end kind
    pure (p, m, a)
    where
        title :: Prod r Text (Located Token) [Token]
        title = bracket (many (unLocated <$> satisfy (\ltok -> unLocated ltok /= BracketR)))

-- 'env_' is like 'env', but without allowing titles.
--
envPos_ :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) (SourcePos, a)
envPos_ kind body = (,) <$> begin kind <*> (optional label *> body) <* end kind

env_ :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) a
env_ kind body = begin kind *> optional label *> body <* end kind

-- | A label specifying a marker for referencing via /@\\label{...}@/. Returns the marker text.
label :: Prod r Text (Located Token) Marker
label = label_ <?> "\"\\label{...}\""
    where
        label_ = terminal \ltok -> case unLocated ltok of
            Label m -> Just (Marker m)
            _tok -> Nothing

-- | A reference via /@\\ref{...}@/. Returns the markers as text.
ref :: Prod r Text (Located Token) (NonEmpty Marker)
ref = terminal \ltok -> case unLocated ltok of
    Ref ms -> Just (Marker <$> ms)
    _tok -> Nothing

math :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
math body = beginMath *> body <* endMath

text :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
text body = begin "text" *> body <* end "text" <?> "\"\\text{...}\""

beginMath, endMath :: Prod r Text (Located Token) SourcePos
beginMath = begin "math" <?> "start of a formula, e.g. \"$\""
endMath = end "math" <?> "end of a formula, e.g. \"$\""

paren :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
paren body = token ParenL *> body <* token ParenR <?> "\"(...)\""

bracket :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
bracket body = token BracketL *> body <* token BracketR <?> "\"[...]\""

brace :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
brace body = token VisibleBraceL  *> body <* token VisibleBraceR <?> "\"\\{...\\}\""

group :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
group body = token InvisibleBraceL *> body <* token InvisibleBraceR <?> "\"{...}\""

align :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
align body = begin "align*" *> body <* end "align*"


maybeVarToken :: Located Token -> Maybe VarSymbol
maybeVarToken ltok = case unLocated ltok of
    Variable x -> Just (NamedVar x)
    _tok -> Nothing

maybeWordToken :: Located Token -> Maybe Text
maybeWordToken ltok = case unLocated ltok of
    Word n -> Just n
    _tok -> Nothing

maybeIntToken :: Located Token -> Maybe Int
maybeIntToken ltok = case unLocated ltok of
    Integer n -> Just n
    _tok -> Nothing

maybeCmdToken :: Located Token -> Maybe Text
maybeCmdToken ltok = case unLocated ltok of
    Command n -> Just n
    _tok -> Nothing

structSymbol :: StructSymbol -> Prod r Text (Located Token) StructSymbol
structSymbol s@(StructSymbol c) = terminal \ltok -> case unLocated ltok of
    Command c' | c == c' -> Just s
    _ -> Nothing

-- | Tokens that are allowed to appear in labels of environments.
maybeTagToken :: Located Token -> Maybe Text
maybeTagToken ltok = case unLocated ltok of
    Symbol "'" ->Just "'"
    Symbol "-" -> Just ""
    _ -> maybeWordToken ltok


token :: Token -> Prod r Text (Located Token) Token
token tok = terminal maybeToken <?> tokToText tok
    where
        maybeToken ltok = case unLocated ltok of
            tok' | tok == tok' -> Just tok
            _ -> Nothing

tokenPos :: Token -> Prod r Text (Located Token) SourcePos
tokenPos tok = terminal maybeToken <?> tokToText tok
    where
        maybeToken ltok = case unLocated ltok of
            tok' | tok == tok' -> Just (startPos ltok)
            _ -> Nothing
