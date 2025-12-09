{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}


module Checking where


import Base
import StructGraph
import Syntax.Internal
import Syntax.Lexicon
import Encoding
import Tptp.UnsortedFirstOrder qualified as Tptp

import Bound.Scope
import Bound.Var (Var(..), unvar)
import Control.Exception (Exception)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Strict
import Data.DList qualified as DList
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.InsOrdMap (InsOrdMap)
import Data.InsOrdMap qualified as InsOrdMap
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.FilePath.Posix
import Text.Megaparsec (SourcePos)
import UnliftIO.Directory

type Checking = CheckingM ()
type CheckingM = StateT CheckingState (WriterT (DList Task) IO)

check :: WithDumpPremselTraining -> Lexicon -> [Block] -> IO [Task]
check dumpPremselTraining lexicon blocks = do
    tasks <- execWriterT (runStateT (checkBlocks blocks) initialCheckingState)
    pure (DList.toList tasks)
    where
        initialCheckingState = CheckingState
            { checkingAssumptions = []
            , checkingDumpPremselTraining = dumpPremselTraining
            , checkingGoals = []
            , checkingFacts = mempty
            , checkingDirectness = Direct
            , checkingAbbreviations = initAbbreviations
            , checkingPredicateDefinitions = mempty
            , checkingStructs = initCheckingStructs
            , instantiatedStructs = Set.empty
            , instantiatedStructOps = HM.empty
            , definedMarkers = HS.empty
            , checkingLexicon = lexicon
            , blockLabel = Marker ""
            , fixedVars = mempty
            }

data WithDumpPremselTraining = WithoutDumpPremselTraining | WithDumpPremselTraining

-- | The checking state accumulates the proof tasks and
-- helps to keep track of the surrounding context.
-- INVARIANT: All formulas in the checking state that eventually
-- get exported should have all their abbreviations resolved.
data CheckingState = CheckingState
    { checkingLexicon :: Lexicon -- For debugging and dumping training data.

    , checkingDumpPremselTraining :: WithDumpPremselTraining

    , checkingAssumptions :: [Formula]
    -- ^ Local assumption.
    --
    , checkingGoals :: [Formula]
    -- ^ The current goals.
    --
    , checkingFacts :: InsOrdMap Marker Formula
    -- ^ Axioms and proven results.
    --
    --
    , checkingDirectness :: Directness
    -- ^ E can detect contradictory axioms and warns about them.
    -- In an indirect proof (e.g. a proof by contradiction) we want
    -- to ignore that warning.
    --
    , checkingAbbreviations :: HashMap Symbol (Scope Int ExprOf Void)
    -- ^ Abbreviations are definitions that automatically get expanded.
    -- They are given by a closed rhs (hence the 'Void' indicating no free variables).
    -- INVARIANT: The bound 'Int' values must be lower than the arity of the symbol.
    --
    , checkingPredicateDefinitions :: HashMap Predicate [Scope Int ExprOf Void]
    -- ^ Definitions of predicate that we can match against in assumptions.
    -- Axioms and theorems that have the shape of a definition can be added as alternate definitions.
    --
    , checkingStructs :: StructGraph
    -- ^ Graph of structs defined so far.
    --
    , instantiatedStructs :: Set VarSymbol
    -- ^ For checking which structure names are in scope to cast them to their carrier.
    --
    , instantiatedStructOps :: HashMap StructSymbol VarSymbol
    -- ^ For annotation of structure operations.
    --
    , fixedVars :: Set VarSymbol
    -- ^ Keeps track of the variables that are locally constant (either introduced implicitly in the assumption or explicitly through the proof steps "take" or "fix").
    --
    , definedMarkers :: HashSet Marker
    -- ^ Markers for toplevel sections need to be unique. This keeps track of the
    -- markers used thus far.
    --
    , blockLabel :: Marker
    -- ^ Label/marker of the current block
    }

initCheckingStructs :: StructGraph
initCheckingStructs = StructGraph.insert
    _Onesorted
    mempty -- no parents
    (Set.singleton CarrierSymbol) -- used for casting X -> \carrier[X]
    mempty -- empty graph

initAbbreviations :: HashMap Symbol (Scope Int ExprOf Void)
initAbbreviations = HM.fromList
    [ (SymbolPredicate (PredicateRelation (Command "notin")), toScope (TermVar (B 0) `IsNotElementOf` TermVar (B 1)))
    , (SymbolPredicate (PredicateVerb (unsafeReadPhraseSgPl "equal[s/] ?")), toScope (TermVar (B 0) `Equals` TermVar (B 1)))
    , (SymbolPredicate (PredicateNoun (unsafeReadPhraseSgPl "element[/s] of ?")), toScope (TermVar (B 0) `IsElementOf` TermVar (B 1)))
    ]

data CheckingError
    = DuplicateMarker SourcePos Marker
    | ByContradictionOnMultipleGoals Marker
    | BySetInductionSyntacticMismatch Marker
    | ProofWithoutPrecedingTheorem Marker
    | CouldNotEliminateHigherOrder FunctionSymbol Term Marker
    | AmbiguousInductionVar Marker
    | MismatchedSetExt [Formula] Marker
    | MismatchedAssume Formula Formula Marker
    deriving (Show, Eq)

instance Exception CheckingError

throwWithMarker :: (Marker -> CheckingError) -> CheckingM a
throwWithMarker err = do
    m <- gets blockLabel
    throwIO (err m)

assume :: [Asm] -> Checking
assume asms = traverse_ go asms
    where
        go :: Asm -> Checking
        go = \case
            Asm phi -> do
                phi' <- canonicalize phi
                modify \st ->
                    st{ checkingAssumptions = phi' : checkingAssumptions st
                    , fixedVars = freeVars phi' <> fixedVars st
                    }
            AsmStruct x sp ->
                instantiateStruct x sp


instantiateStruct :: VarSymbol -> StructPhrase -> Checking
instantiateStruct x sp = do
    st <- get
    let structGraph = checkingStructs st
    let struct = lookupStruct structGraph sp
    let fixes = StructGraph.structSymbols struct structGraph
    let phi = (TermSymbol (SymbolPredicate (PredicateNounStruct sp)) [TermVar x])
    --
    -- NOTE: this will always cause shadowing of operations, ideally this should be type-directed instead.
    let ops = HM.fromList [(op, x) | op <- Set.toList fixes]
    put st
            { instantiatedStructs = Set.insert x (instantiatedStructs st)
            , instantiatedStructOps = ops <> instantiatedStructOps st -- left-biased union
            , checkingAssumptions = phi : checkingAssumptions st
            }


lookupStruct :: StructGraph -> StructPhrase -> Struct
lookupStruct structGraph struct = case StructGraph.lookup struct structGraph of
    Just result -> result
    Nothing -> error $ "lookup of undefined structure: " <> show struct


-- | Replace all current goals with a new goal. Use with care!
setGoals :: [Formula] -> Checking
setGoals goals = do
    goals <- traverse canonicalize goals
    modify $ \st -> st{checkingGoals = goals}


-- | Create (and add) tasks based on facts, local assumptions, and goals.
tellTasks :: Checking
tellTasks = do
    goals <- gets checkingGoals
    m <- gets blockLabel
    facts <- liftA2 (<>) (gets checkingFacts) (withMarker m <$> gets checkingAssumptions)
    directness <- gets checkingDirectness
    let tasks = DList.fromList (Task directness (InsOrdMap.toList facts) m <$> goals)
    tell tasks

withMarker :: Marker -> [v] -> InsOrdMap Marker v
withMarker (Marker m) phis = InsOrdMap.fromList $ zipWith (\phi k -> (Marker (m <> Text.pack (show k)), phi)) phis ([1..] :: [Int])

-- | Make a fact available to all future paragraphs.
addFact :: Formula -> Checking
addFact phi = do
    phi' <- canonicalize phi
    m <- gets blockLabel
    modify $ \st -> st{checkingFacts = InsOrdMap.insert m phi' (checkingFacts st)}


-- | Make a fact available to all future paragraphs.
addFacts :: InsOrdMap Marker Formula -> Checking
addFacts phis = do
    phis' <- forM phis canonicalize
    modify $ \st -> st{checkingFacts = phis' <> (checkingFacts st)}





addFactWithAsms :: [Asm] -> Formula -> Checking
addFactWithAsms asms stmt = do
    (asms', structs, structOps) <- mergeAssumptions asms
    asms'' <- traverse (canonicalizeWith structs structOps) asms'
    stmt' <- canonicalizeWith structs structOps stmt
    m <- gets blockLabel
    modify $ \st ->
        let phi = case asms'' of
                [] -> forallClosure mempty stmt'
                _ -> forallClosure mempty (makeConjunction asms'' `Implies` stmt')
        in st{checkingFacts = InsOrdMap.insert m phi (checkingFacts st)}


-- | Mark a proof as indirect. Intended to be used in a @locally do@ block.
byContradiction :: Checking
byContradiction = do
    st <- get
    case checkingGoals st of
        [goal] -> put st{checkingGoals = [Bottom], checkingDirectness = Indirect goal}
        goals -> error ("multiple or no goal in proof by contradiction" <> show goals)


unabbreviateWith :: (forall a. HashMap Symbol (Scope Int ExprOf a)) -> (forall b. ExprOf b -> ExprOf b)
unabbreviateWith abbrs = unabbr
    where
        unabbr :: ExprOf b -> ExprOf b
        unabbr = \case
            TermSymbol sym es ->
                let es' = unabbr <$> es
                in case HM.lookup sym abbrs of
                        Nothing -> TermSymbol sym es'
                        Just scope -> unabbr (instantiate (\k -> nth k es ?? error "unabbreviateWith: incorrect index") scope)
            Not e ->
                Not (unabbr e)
            Apply e es ->
                Apply (unabbr e) (unabbr <$> es)
            TermSep vs e scope ->
                TermSep vs (unabbr e) (hoistScope unabbr scope)
            ReplacePred y x xB scope ->
                ReplacePred y x xB (hoistScope unabbr scope)
            ReplaceFun bounds scope cond ->
                ReplaceFun ((\(x, e) -> (x, unabbr e)) <$> bounds) (hoistScope unabbr scope) (hoistScope unabbr cond)
            Connected con e1 e2 ->
                Connected con (unabbr e1) (unabbr e2)
            Lambda scope ->
                Lambda  (hoistScope unabbr scope)
            Quantified quant scope      ->
                Quantified quant (hoistScope unabbr scope)
            e@PropositionalConstant{} ->
                e
            e@TermVar{} ->
                e
            TermSymbolStruct symb e ->
                TermSymbolStruct symb (unabbr <$> e)

-- | Unroll comprehensions in equations.
-- E.g. /@B = \\{f(a) | a\\in A \\}@/ turns into
-- /@\\forall b. b\\in B \\iff \\exists a\\in A. b = f(a)@/.
desugarComprehensions :: forall a. ExprOf a -> ExprOf a
desugarComprehensions = \case
     -- We only desugar comprehensions under equations. We do not allow nesting.
    e@TermSep{} -> e
    e@ReplacePred{} -> e
    e@ReplaceFun{} -> e
    e@TermVar{} -> e
    e@PropositionalConstant{} -> e
    e@TermSymbolStruct{}-> e
    --
    e `Equals` TermSep x bound scope -> desugarSeparation e x bound scope
    TermSep x bound scope `Equals` e -> desugarSeparation e x bound scope
    --
    e `Equals` ReplaceFun bounds scope cond -> makeReplacementIff (F <$> e) bounds scope cond
    ReplaceFun bounds scope cond `Equals` e -> makeReplacementIff (F <$> e) bounds scope cond
    --
    Apply e es -> Apply (desugarComprehensions e) (desugarComprehensions <$> es)
    Not e -> Not (desugarComprehensions e)
    TermSymbol sym es -> TermSymbol sym (desugarComprehensions <$> es)
    Connected conn e1 e2 -> Connected conn (desugarComprehensions e1) (desugarComprehensions e2)
    Lambda scope -> Lambda (hoistScope desugarComprehensions scope)
    Quantified quant scope -> Quantified quant (hoistScope desugarComprehensions scope)
    where
        desugarSeparation :: ExprOf a -> VarSymbol -> (ExprOf a) -> (Scope () ExprOf a) -> ExprOf a
        desugarSeparation e x bound scope =
            let phi = (TermVar (B x) `IsElementOf` (F <$> e)) :: ExprOf (Var VarSymbol a)
                psi = (TermVar (B x) `IsElementOf` (F <$> bound)) :: ExprOf (Var VarSymbol a)
                rho = fromScope (mapBound (const x) scope)
            in  Quantified Universally (toScope (phi `Iff` (psi `And` rho)))


desugarComprehensionsA :: Applicative f => ExprOf a -> f (ExprOf a)
desugarComprehensionsA e = pure (desugarComprehensions e)




checkBlocks :: [Block] -> Checking
checkBlocks = \case
    BlockAxiom pos marker axiom : blocks -> do
        withLabel pos marker (checkAxiom axiom)
        checkBlocks blocks
    BlockDefn pos marker defn : blocks -> do
        withLabel pos marker (checkDefn defn)
        checkBlocks blocks
    BlockAbbr pos marker abbr : blocks -> do
        withLabel pos marker  (checkAbbr abbr)
        checkBlocks blocks
    BlockLemma pos marker lemma : BlockProof _pos2 proof : blocks -> do
        withLabel pos marker (checkLemmaWithProof lemma proof)
        checkBlocks blocks
    BlockLemma pos marker  lemma : blocks -> do
        withLabel pos marker (checkLemma lemma)
        checkBlocks blocks
    BlockProof _pos _proof : _ ->
        throwWithMarker ProofWithoutPrecedingTheorem
    BlockSig _pos asms sig : blocks -> do
        checkSig asms sig
        checkBlocks blocks
    BlockInductive pos marker inductiveDefn : blocks -> do
        withLabel pos marker (checkInductive inductiveDefn)
        checkBlocks blocks
    BlockStruct pos marker structDefn : blocks -> do
        withLabel pos marker (checkStructDefn structDefn)
        checkBlocks blocks
    [] -> skip

-- | Add the given label to the set of in-scope markers and set it as the current label for error reporting.
withLabel :: SourcePos -> Marker -> CheckingM a -> CheckingM a
withLabel pos marker ma = do
    -- Add a new marker to the set. It is a checking error if the marker has already been used.
    st <- get
    let markers = definedMarkers st
    if HS.member marker markers
        then throwWithMarker (DuplicateMarker pos)
        else put st{definedMarkers = HS.insert marker markers}
    -- Set the marker as the label of the current block.
    modify \st -> st{blockLabel = marker}
    ma

-- | Verification of a lemma with a proof.
-- We skip omitted proofs and treat them as proper gaps of the formalization.
-- This is useful when developing a formalization, as it makes it easy to
-- leave difficult proofs for later.
checkLemmaWithProof :: Lemma -> Proof -> Checking
checkLemmaWithProof (Lemma asms goal) proof = do
    locally do
        assume asms
        setGoals [goal]
        checkProof proof
    addFactWithAsms asms goal


-- | Verification of a lemma without a proof.
checkLemma :: Lemma -> Checking
checkLemma (Lemma asms goal) = do
    locally do
        assume asms
        setGoals [goal]
        tellTasks
    -- Make fact from asms and stmt (take universal closure).
    addFactWithAsms asms goal


checkAxiom :: Axiom -> Checking
checkAxiom (Axiom asms axiom) = addFactWithAsms asms axiom

checkProof :: Proof -> Checking
checkProof = \case
    Qed pos JustificationEmpty->
        tellTasks
    Qed pos JustificationSetExt -> do
        goals <- gets checkingGoals
        case goals of
            [goal] -> do
                goals' <- splitGoalWithSetExt goal
                setGoals goals'
                tellTasks
            [] -> pure ()
            _ -> throwWithMarker (MismatchedSetExt goals)
    Qed pos (JustificationRef ms) ->
        byRef ms
    Qed pos JustificationLocal ->
        byAssumption
    ByContradiction pos proof -> do
        goals <- gets checkingGoals
        case goals of
            [goal] -> do
                assume [Asm (Not goal)]
                byContradiction
                checkProof proof
            _ -> throwWithMarker ByContradictionOnMultipleGoals
    ByCase pos splits -> do
        for_ splits checkCase
        setGoals [makeDisjunction (caseOf <$> splits)]
        tellTasks
    BySetInduction pos mx continue -> do
        goals <- gets checkingGoals
        case goals of
            Forall scope : goals' -> do
                let zs = nubOrd (bindings scope)
                z <- case mx of
                    Nothing -> case zs of
                        [z'] -> pure z'
                        _ -> throwWithMarker AmbiguousInductionVar
                    Just (TermVar z') -> pure z'
                    _ -> do
                        m <- gets blockLabel
                        throwIO (AmbiguousInductionVar m)
                let y = NamedVar "IndAntecedent"
                let ys = List.delete z zs
                let anteInst bv = if bv == z then TermVar y else TermVar bv
                let antecedent = makeForall (y : ys) ((TermVar y `IsElementOf` TermVar z) `Implies` instantiate anteInst scope)
                assume [Asm antecedent]
                let consequent = instantiate TermVar scope
                setGoals (consequent : goals')
                checkProof continue
            _ -> do
                m <- gets blockLabel
                throwIO (BySetInductionSyntacticMismatch m)
    ByOrdInduction pos continue -> do
        goals <- gets checkingGoals
        case goals of
            Forall scope : goals' -> case fromScope scope of
                Implies (IsOrd (TermVar (B bz))) rhs -> do
                    let zs = nubOrd (bindings scope)
                    z <- case zs of
                            [z'] | z' == bz -> pure z'
                            [_] -> error "induction variable does not match the variable with ordinal guard"
                            _ -> throwWithMarker AmbiguousInductionVar
                    -- LATER: this is kinda sketchy:
                    -- we now use the induction variable in two ways:
                    -- we assume the induction hypothesis, where we recycle the induction variable both as a bound variable and a free variable
                    -- we then need to show that under that hypothesis the claim holds for the free variable...
                    let hypo = Forall (toScope (Implies ((TermVar (B z)) `IsElementOf` (TermVar (F z))) rhs))
                    assume [Asm (IsOrd (TermVar z)), Asm hypo]
                    let goal' = unvar id id <$> rhs -- we "instantiate" the single bound variable on the rhs
                    setGoals (goal' : goals')
                    checkProof continue
                _ -> error ("could not match transfinite induction with syntactic structure of the first goal: " <> show goals)
            _ -> error ("the first goal must be universally quantifier to apply transfinite induction: " <> show goals)
    Assume pos phi continue -> do
        goals' <- matchAssumptionWithGoal phi
        assume [Asm phi]
        setGoals goals'
        checkProof continue
    Fix pos xs suchThat continue -> do
        fixing xs
        checkProof case suchThat of
            Top -> continue
            _ ->  Assume pos suchThat continue
    Subclaim pos subclaim subproof continue -> do
        locally (checkLemmaWithProof (Lemma [] subclaim) subproof)
        assume [Asm subclaim]
        checkProof continue
    Omitted -> do
        setGoals []
    Suffices pos reduction by proof -> do
        goals <- gets checkingGoals
        setGoals [reduction `Implies` makeConjunction goals]
        justify by
        setGoals [reduction]
        checkProof proof
    Take pos _witnesses _suchThat JustificationSetExt _continue ->
        error $ "Error at " <> show pos <> "\nCannot justify existential statement with setext"
    Take pos witnesses suchThat by continue -> locally do
        goals <- gets checkingGoals
        setGoals [makeExists witnesses suchThat]
        justify by
        assume [Asm suchThat]
        setGoals goals
        checkProof continue
    Have pos claim (JustificationRef ms) continue -> locally do
        goals <- gets checkingGoals
        setGoals [claim]
        byRef ms -- locally prove things with just refs and local assumptions
        assume [Asm claim]
        setGoals goals
        checkProof continue
    Have pos claim JustificationLocal continue -> locally do
        goals <- gets checkingGoals
        setGoals [claim]
        byAssumption -- locally prove things with just local assumptions
        assume [Asm claim]
        setGoals goals
        checkProof continue
    Have pos claim by continue -> do
        locally do
            goals <- gets checkingGoals
            claims <- case by of
                JustificationEmpty ->
                    pure [claim]
                JustificationSetExt ->
                    splitGoalWithSetExt claim
                -- NOTE: we already handled @JustificationRef ms@ and GHC recognizes this
            setGoals claims
            tellTasks
            assume [Asm claim]
            setGoals goals
            checkProof continue
    Define pos x t continue -> locally do
        assume [Asm case t of
            TermSep y yBound phi ->
                makeForall [y] $
                    Iff (TermVar y `IsElementOf` TermVar x)
                        ((TermVar y `IsElementOf` yBound) `And` instantiate1 (TermVar y) phi)
            ReplaceFun bounds lhs cond ->
                makeReplacementIff (TermVar (F x)) bounds lhs cond
            _ -> Equals (TermVar x) t
            ]
        checkProof continue
    DefineFunction pos funVar argVar valueExpr domExpr continue -> do
        -- we're given f, x, e, d
        assume
            [ Asm (TermOp DomSymbol [TermVar funVar] `Equals` domExpr) -- dom(f) = d
            , Asm (makeForall [argVar] ((TermVar argVar `IsElementOf` domExpr) `Implies` (TermOp ApplySymbol [TermVar funVar, TermVar argVar] `Equals` valueExpr))) -- f(x) = e for all x\in d
            , Asm (rightUniqueAdj (TermVar funVar))
            , Asm (relationNoun (TermVar funVar))
            ]
        checkProof continue
    Calc pos quant calc continue -> do
        checkCalc quant calc
        assume [Asm (calcResult quant calc)]
        checkProof continue
    DefineFunctionLocal pos funVar argVar domVar ranExpr definitions continue -> do
        -- We have f: X \to Y and x \mapsto ...
        -- definition is a nonempty list of (expresssion e, formula phi)
        -- such that f(x) =  e if phi(x)
        -- since we do a case deduction in the definition there has to be a check that,
        -- our domains in the case are a disjunct union of dom(f)
        assume
            [Asm (TermOp DomSymbol [TermVar funVar] `Equals` TermVar domVar)
            ,Asm (rightUniqueAdj (TermVar funVar))
            ,Asm (relationNoun (TermVar funVar))]

        goals <- gets checkingGoals
        setGoals [makeForall [argVar] ((TermVar argVar `IsElementOf` TermVar domVar) `Iff` localFunctionGoal definitions)]
        tellTasks

        fixed <- gets fixedVars
        assume [Asm (makeForall [argVar] ((TermVar argVar `IsElementOf` TermVar domVar) `Implies` (TermOp ApplySymbol [TermVar funVar, TermVar argVar] `IsElementOf` ranExpr)))] -- function f from \dom(f) \to \ran(f)
        assume (functionSubdomianExpression funVar argVar domVar fixed (NonEmpty.toList definitions)) --behavior on the subdomians
        setGoals goals
        checkProof continue

-- |Creats the Goal \forall x. x \in dom{f} \iff (phi_{1}(x) \xor (\phi_{2}(x) \xor (... \xor (\phi_{n}) ..)))
--  where the phi_{i} are the subdomain statments
localFunctionGoal :: NonEmpty (Term,Formula) -> Formula
localFunctionGoal xs = makeXor $ map snd $ NonEmpty.toList xs


-- We have our list of expr and forumlas, in this case normaly someone would write
-- f(x) =  ....cases
--      & (\frac{1}{k} \cdot x) &\text{if} x \in \[k, k+1\)
--
-- since we have to bind all globaly free Varibels we generate following asumptions.
--
-- For    x \mapsto  expr(x,ys,cs) , if formula(x,ys)        ; here cs are just global constants
--          ->   \forall x,ys: ( formula(x,ys) => expr(x,ys,cs))


functionSubdomianExpression :: VarSymbol -> VarSymbol -> VarSymbol -> Set VarSymbol -> [(Term, Formula)] -> [Asm]
functionSubdomianExpression f a d s (x:xs) = singleFunctionSubdomianExpression f a d s x : functionSubdomianExpression f a d s xs
functionSubdomianExpression _ _ _ _ [] = []

singleFunctionSubdomianExpression :: VarSymbol -> VarSymbol -> VarSymbol -> Set VarSymbol -> (Term, Formula) -> Asm
singleFunctionSubdomianExpression funVar argVar domVar fixedV (expr, frm) = let
    -- boundVar = Set.toList (freeVars expr) in
    -- let def = makeForall (argVar:boundVar) (((TermVar argVar `IsElementOf` TermVar domVar) `And` frm) `Implies` TermOp ApplySymbol [TermVar funVar, TermVar argVar] `Equals` expr)
    boundVar = fixedV in
    let def = forallClosure boundVar (((TermVar argVar `IsElementOf` TermVar domVar) `And` frm) `Implies` (TermOp ApplySymbol [TermVar funVar, TermVar argVar] `Equals` expr))
    in Asm def



checkCalc :: CalcQuantifier -> Calc -> Checking
checkCalc quant calc = locally do
    let tasks = calculation quant calc
    forM_ tasks tell
    where
        tell = \case
            (goal, by) -> setGoals [goal] *> justify by


makeReplacementIff
    :: forall a. (ExprOf (Var VarSymbol a) -- ^ Newly defined local constant.
    -> NonEmpty (VarSymbol, ExprOf a) -- ^ Bounds of the replacement.
    -> Scope VarSymbol ExprOf a -- ^ Left hand side (function application).
    -> Scope VarSymbol ExprOf a -- ^ Optional constraints on bounds (can just be 'Top').
    -> ExprOf a)
makeReplacementIff e bounds lhs cond =
    Forall (toScope (Iff (TermVar (B "frv") `IsElementOf` e)  existsPreimage))
      where
        existsPreimage :: ExprOf (Var VarSymbol a)
        existsPreimage = Exists (toScope replaceBound)

        replaceBound :: ExprOf (Var VarSymbol (Var VarSymbol a))
        replaceBound = makeConjunction [TermVar (B x) `IsElementOf` (F . F <$> xB) | (x, xB) <- toList bounds] `And` replaceCond

        replaceEq :: ExprOf (Var VarSymbol (Var VarSymbol a))
        replaceEq = (nestF <$> fromScope lhs) `Equals` TermVar (F (B "frv"))

        replaceCond :: ExprOf (Var VarSymbol (Var VarSymbol a))
        replaceCond = case fromScope cond of
            Top -> replaceEq
            cond' -> replaceEq `And` (F <$> cond')

        nestF :: Var b a1 -> Var b (Var b1 a1)
        nestF (B a) = B a
        nestF (F a) = F (F a)


splitGoalWithSetExt :: Formula -> CheckingM [Formula]
splitGoalWithSetExt = \case
    NotEquals x y -> do
        let z = FreshVar 0
            elemNotElem x' y' = makeExists [FreshVar 0] (And (TermVar z `IsElementOf` x') ((TermVar z `IsNotElementOf` y')))
        pure [elemNotElem x y `Or` elemNotElem y x]
    Equals x y -> do
        let z = FreshVar 0
            subset x' y' = makeForall [FreshVar 0] (Implies (TermVar z `IsElementOf` x') ((TermVar z `IsElementOf` y')))
        pure [subset x y, subset y x]
    goal -> throwWithMarker (MismatchedSetExt [goal])

justify :: Justification -> Checking
justify = \case
    JustificationEmpty -> tellTasks
    JustificationLocal -> byAssumption
    JustificationRef ms -> byRef ms
    JustificationSetExt -> do
        goals <- gets checkingGoals
        case goals of
            [goal] -> do
                goals' <- splitGoalWithSetExt goal
                setGoals goals'
                tellTasks
            _ -> throwWithMarker (MismatchedSetExt goals)

byRef :: NonEmpty Marker -> Checking
byRef ms = locally do
    facts <- gets checkingFacts
    dumpPremselTraining <- gets checkingDumpPremselTraining
    case dumpPremselTraining of
        WithDumpPremselTraining -> dumpTrainingData facts ms
        WithoutDumpPremselTraining -> skip
    case InsOrdMap.lookupsMap ms facts of
        Left (Marker str) -> error ("unknown marker: " <> Text.unpack str)
        Right facts' -> modify (\st -> st{checkingFacts = facts'}) *> tellTasks

byAssumption :: Checking
byAssumption = locally do
    modify (\st -> st{checkingFacts = mempty}) *> tellTasks

dumpTrainingData :: InsOrdMap Marker Formula -> NonEmpty Marker -> Checking
dumpTrainingData facts ms = do
    let (picked, unpicked) = InsOrdMap.pickOutMap ms facts
    lexicon <- gets checkingLexicon
    goals <- gets checkingGoals
    m@(Marker m_) <- gets blockLabel
    _localFacts <- withMarker m <$> gets checkingAssumptions
    let dir = "premseldump"
    let makePath k = dir </> (Text.unpack m_ <> show (k :: Int)) <.> "txt"
    let dumpTrainingExample goal =
            let conj = encodeConjecture lexicon m goal
                usefuls = encodeWithRole Tptp.AxiomUseful lexicon (InsOrdMap.toList picked)
                redundants = encodeWithRole Tptp.AxiomRedundant lexicon (InsOrdMap.toList unpicked)
                k = hash goal
                example = Tptp.toTextNewline (Tptp.Task (conj : (usefuls <> redundants)))
            in do
                liftIO (Text.writeFile (makePath k) example)
    liftIO (createDirectoryIfMissing True dir)
    forM_ goals dumpTrainingExample

-- | Since the case tactic replaces /all/ current goals with the disjunction
-- of the different case hypotheses, each case proof must cover all goals.
checkCase :: Case -> Checking
checkCase (Case split proof) = locally do
        assume [Asm split]
        checkProof proof


checkDefn :: Defn -> Checking
checkDefn = \case
    DefnPredicate asms symb vs f -> do
        -- We first need to take the universal closure of the defining formula
        -- while ignoring the variables that occur on the lhs, then take the
        -- universal formula of the equivalence, quantifying the remaining
        -- variables (from the lhs).
        let vs' = TermVar <$> toList vs
        let f' = forallClosure (Set.fromList (toList vs)) f
        addFactWithAsms asms (Atomic symb vs' `Iff` f')
    DefnFun asms fun vs rhs -> do
        let lhs = TermSymbol (SymbolFun fun) (TermVar <$> vs)
        addFactWithAsms asms (lhs `Equals` rhs)
    -- TODO Check that the function symbol on the lhs does not appear on the rhs.
    DefnOp op vs (TermSep x bound phi) ->
        addFact $ makeForall (x : vs) $
            Iff (TermVar x `IsElementOf` TermOp op (TermVar <$> vs))
                ((TermVar x `IsElementOf` bound) `And` instantiate1 (TermVar x) phi)
    DefnOp op vs (TermSymbol symbol [x, y]) | symbol == SymbolMixfix ConsSymbol -> do
        -- TODO generalize this to support arbitrarily many applications of _Cons
        -- and also handle the case of emptyset or singleton as final argument separately
        -- so that finite set terms get recognized in full.
        let phi = TermVar "any" `IsElementOf` TermOp op (TermVar <$> vs)
        let psi = (TermVar "any" `IsElementOf` y) `Or` (TermVar "any" `Equals` x)
        addFact (makeForall ("any" : vs) (phi `Iff` psi))
    DefnOp op vs (ReplacePred _y _x xBound scope) -> do
        let x  = (FreshVar 0)
        let y  = (FreshVar 1)
        let y' = (FreshVar 2)
        let fromReplacementVar = \case
                ReplacementDomVar -> TermVar x
                ReplacementRangeVar -> TermVar y
        let fromReplacementVar' = \case
                ReplacementDomVar -> TermVar x
                ReplacementRangeVar -> TermVar y'
        let phi = instantiate fromReplacementVar scope
        let psi = instantiate fromReplacementVar' scope
        let singleValued = makeForall [x] ((TermVar x `IsElementOf` xBound) `Implies` makeForall [y, y'] ((phi `And` psi) `Implies` (TermVar y `Equals` TermVar y')))
        setGoals [singleValued]
        tellTasks
        addFact (makeForall (y : vs) ((TermVar y `IsElementOf` TermOp op (TermVar <$> vs)) `Iff` makeExists [x] ((TermVar x `IsElementOf` xBound) `And` phi)))

    DefnOp op vs (ReplaceFun bounds lhs cond) ->
        addFact (forallClosure mempty (makeReplacementIff (TermOp op (TermVar . F <$> vs)) bounds lhs cond))
    DefnOp op vs rhs ->
        if containsHigherOrderConstructs rhs
            then throwWithMarker(CouldNotEliminateHigherOrder op rhs)
            else do
                let lhs = TermSymbol (SymbolMixfix op) (TermVar <$> vs)
                addFactWithAsms [] (lhs `Equals` rhs)


checkSig :: [Asm] -> Signature -> Checking
checkSig asms sig = case sig of
        SignatureFormula f ->
            addFactWithAsms asms f
        SignaturePredicate _predi _vs -> do
            skip -- TODO

-- | Annotate plain structure operations in a formula with the label of a suitable in-scope struct.
annotateStructOps :: Formula -> CheckingM Formula
annotateStructOps phi = do
    ops <- gets instantiatedStructOps
    labels <- gets instantiatedStructs
    pure (annotateWith labels ops phi)


mergeAssumptions :: [Asm] -> CheckingM ([Formula], Set VarSymbol, HashMap StructSymbol VarSymbol)
mergeAssumptions [] = pure ([], mempty, mempty)
mergeAssumptions (asm : asms) = case asm of
    Asm phi ->
        (\(phis, xs, ops) -> (phi : phis, xs, ops)) <$> mergeAssumptions asms
    AsmStruct x phrase -> do
        st <- get
        let structGraph = checkingStructs st
        let struct = lookupStruct structGraph phrase
        let fixes = StructGraph.structSymbols struct structGraph
        let ops' = HM.fromList [(op, x) | op <- Set.toList fixes]
        (\(phis, xs, ops) -> (TermSymbol (SymbolPredicate (PredicateNounStruct phrase)) [TermVar x] : phis, Set.insert x xs, ops' <> ops)) <$> mergeAssumptions asms

canonicalize :: Formula -> CheckingM Formula
canonicalize = unabbreviate >=> annotateStructOps >=> desugarComprehensionsA

canonicalizeWith :: Set VarSymbol -> HashMap StructSymbol VarSymbol -> Formula -> CheckingM Formula
canonicalizeWith labels ops = unabbreviate >=> annotateWithA labels ops >=> desugarComprehensionsA

annotateWithA :: Applicative f => Set VarSymbol -> HashMap StructSymbol VarSymbol -> Formula -> f Formula
annotateWithA labels ops phi = pure (annotateWith labels ops phi)

unabbreviate :: ExprOf a -> CheckingM (ExprOf a)
unabbreviate phi = do
    abbrs <- gets checkingAbbreviations
    pure (unabbreviateWith ((absurd <$>) <$> abbrs) phi)



checkInductive :: Inductive -> Checking
checkInductive Inductive{..} = do
    forM inductiveIntros (checkIntroRule inductiveSymbol inductiveParams inductiveDomain)
    addFact (forallClosure mempty (TermOp inductiveSymbol (TermVar <$> inductiveParams) `IsSubsetOf` inductiveDomain))
    forM_ inductiveIntros addIntroRule

addIntroRule :: IntroRule -> Checking
addIntroRule (IntroRule conditions result) = addFact (forallClosure mempty (makeConjunction conditions `Implies` result))

checkIntroRule :: FunctionSymbol -> [VarSymbol] -> Expr -> IntroRule -> Checking
checkIntroRule f args dom rule = do
    case isValidIntroRule f args rule of
        Left err -> error err
        Right goals -> case List.filter (/= Top) goals of
            [] -> skip
            goals' -> setGoals goals' *> tellTasks
    setGoals [typecheckRule f args dom rule] *> tellTasks

-- isValidCondition e phi returns 'Right' the needed monotonicity proof tasks if the condition is a valid for an inductive definition of e, and returns 'Left' if the condition is invalid.
isValidCondition :: FunctionSymbol -> [VarSymbol] -> Formula -> Either String Formula
isValidCondition f args phi = if isSideCondition phi
    then Right Top -- Side conditions do not require any monotonicty proofs.
    else monotonicty phi
    where
        -- Side conditions are formulas in which f does not appear.
        isSideCondition :: ExprOf a -> Bool
        isSideCondition = \case
            Not a -> isSideCondition a
            Connected _ a b -> isSideCondition a && isSideCondition b
            TermVar _ -> True
            TermSymbol f' args -> f' /= SymbolMixfix f && all isSideCondition args
            TermSymbolStruct _ Nothing -> True
            TermSymbolStruct _ (Just e) -> isSideCondition e
            Apply a b -> isSideCondition a && all isSideCondition b
            TermSep _ xB cond -> isSideCondition xB && isSideCondition (fromScope cond)
            ReplacePred _ _ e scope -> isSideCondition e && isSideCondition (fromScope scope)
            ReplaceFun bounds lhs rhs ->
                all (\(_, e) -> isSideCondition e) bounds && isSideCondition (fromScope lhs) && isSideCondition (fromScope rhs)
            Lambda body -> isSideCondition (fromScope body)
            Quantified _ body -> isSideCondition (fromScope body)
            PropositionalConstant _ -> True
        -- Potential monotonicity task for conditions in which f appears
        monotonicty = \case
            -- Conditions that are not side conditions must be atomic statements about membership
            _ `IsElementOf` TermOp f' args' | f' == f && args' == (TermVar <$> args) ->
                Right Top -- No monotonicity to prove if the symbols occurs plainly.
            _ `IsElementOf` e ->
                Right (monotone (extractMonotonicFunction e))
            _ -> Left "Intro rule not of the form \"_ \\in h(_) \""
        -- IMPORTANT: we assume that extractMonotonicFunction is applied to a first-order term
        extractMonotonicFunction :: Expr -> (Expr -> Expr)
        extractMonotonicFunction e = \x -> go x e
            where
                go x = \case
                    TermSymbol f' args' -> if
                        | f' == SymbolMixfix f && args' == (TermVar <$> args) -> x
                        | f' == SymbolMixfix f -> error ("symbol " <> show f <> " occurred with the wrong arguments " <> show args')
                        | otherwise -> TermSymbol f' (go x <$> args')
                    TermVar x -> TermVar x
                    e@(TermSymbolStruct _ Nothing) -> e
                    TermSymbolStruct s (Just e') -> TermSymbolStruct s (Just (go x e'))
                    _ -> error "could not extract monotonic function"

isValidResult :: FunctionSymbol -> [VarSymbol] -> Formula -> Bool
isValidResult f args phi = case phi of
    _ `IsElementOf` e | e == TermOp f (TermVar <$> args) -> True
    _ -> False

isValidIntroRule :: FunctionSymbol -> [VarSymbol] -> IntroRule -> Either String [Formula]
isValidIntroRule f args rule = if isValidResult f args (introResult rule)
    then mapM (isValidCondition f args) (introConditions rule)
    else Left "invalid result in rule"

monotone :: (Expr -> Expr) -> Formula
monotone h = makeForall ("xa" : ["xb"])
        ((TermVar "xa" `IsSubsetOf` TermVar "xb") `Implies` (h (TermVar "xa") `IsSubsetOf` h (TermVar "xb")))

typecheckRule :: FunctionSymbol -> [VarSymbol] -> Expr -> IntroRule -> Formula
typecheckRule f args dom (IntroRule conds result) = makeConjunction (go <$> conds) `Implies` go result
    where
        -- replace symbol by dom for TC rule
        go :: Expr -> Expr
        go = \case
            TermSymbol f' args' -> if
                | f' == SymbolMixfix f && args' == (TermVar <$> args) -> dom
                | f' == SymbolMixfix f -> error ("typecheckRule: symbol " <> show f <> " occurred with the wrong arguments " <> show args')
                | otherwise -> TermSymbol f' (go <$> args')
            TermVar x -> TermVar x
            e@(TermSymbolStruct _ Nothing) -> e
            TermSymbolStruct s (Just e') -> TermSymbolStruct s (Just (go e'))
            Not a -> Not (go a)
            Connected conn a b -> Connected conn (go a) (go b)
            Apply a b -> Apply (go a) (go <$> b)
            e@PropositionalConstant{} -> e
            --TermSep x xB cond -> TermSep x (go xB) (hoistScope go cond)
            --ReplacePred x y e scope -> ReplacePred x y (go e) (hoistScope go scope)
            --ReplaceFun bounds lhs rhs ->
            --    ReplaceFun ((\(x, e) -> (x, go e)) <$> bounds) (hoistScope go lhs) (hoistScope go rhs)
            --Lambda body -> Lambda (hoistScope go body)
            --Quantified quant body -> Quantified quant (hoistScope go body)
            _ -> error "typecheckRule does not handle binders"

checkStructDefn :: StructDefn -> Checking
checkStructDefn StructDefn{..} = do
    st <- get
    let structGraph = checkingStructs st
    let m@(Marker m_) = blockLabel st
    let structAncestors = Set.unions (Set.map (`StructGraph.lookupAncestors` structGraph) structParents)
    let structAncestors' = structParents <> structAncestors
    let isStruct p = TermSymbol (SymbolPredicate (PredicateNounStruct p)) [TermVar structDefnLabel]
    let intro = forallClosure mempty if structParents == Set.singleton _Onesorted
            then makeConjunction (snd <$> structDefnAssumes) `Implies` isStruct structPhrase
            else makeConjunction ([isStruct parent | parent <- toList structParents] <> (snd <$> structDefnAssumes)) `Implies` isStruct structPhrase
    let intro' = (m, intro)
    let inherit' = (Marker (m_ <> "inherit"), forallClosure mempty (isStruct structPhrase `Implies` makeConjunction [isStruct parent | parent <- toList structParents]))
    let elims' = [(marker, forallClosure mempty (isStruct structPhrase `Implies` phi)) | (marker, phi) <- structDefnAssumes]
    rules' <- forM (InsOrdMap.fromList (intro' : inherit' : elims')) canonicalize
    put st
            { checkingStructs = StructGraph.insert structPhrase structAncestors' structDefnFixes (checkingStructs st)
            , checkingFacts = rules' <> checkingFacts st
            }

fixing :: NonEmpty VarSymbol -> Checking
fixing xs = do
    goals <- gets checkingGoals
    let (goal, goals') = case goals of
            goal : goals' -> (goal, goals')
            _ -> error "no open goals, cannot use \"fix\" step"
    let goal' = case goal of
            Forall body | [_bv] <- nubOrd (bindings body) ->
                -- If there's only one quantified variable we can freely choose a new name.
                -- This is useful for nameless quantified phrases such as @every _ is an element of _@.
                case xs of
                    x :| [] ->
                        instantiate (\_bv -> TermVar x) body
                    _ ->
                        error "couldn't use fix: only one bound variable but multiple variables to be fixed"
            Forall body | toList xs `List.intersect` nubOrd (bindings body) == toList xs ->
                Forall (instantiateSome xs body)
            Forall body ->
                error ("You can only use \"fix\" if all specified variables occur in the outermost quantifier. Variables to be fixed were: "
                    <> show xs <> " but only the following are bound: " <> show (nubOrd (bindings body)))
            _ ->
                error "you can only use \"fix\" if the goal is universal."
    setGoals (goal' : goals')

-- | An assumption step in a proof is supposed to match the goal.
matchAssumptionWithGoal :: Formula -> CheckingM [Formula]
matchAssumptionWithGoal asm = do
    goals <- gets checkingGoals
    let (goal, goals') = case goals of
            goal : goals' -> (goal, goals')
            _ -> error "no open goals, cannot use assumption step"
    defns <- gets checkingPredicateDefinitions
    case syntacticMatch goal of
        Just phi -> pure (phi : goals')
        --
        -- Unfolding definitions against atomic goals
        Nothing -> case goal of
            phi@(Atomic p args) ->
                let rhos = (HM.lookup p defns ?? [])
                    rhos' = [instantiate (\k -> nth k args ?? error "defns: incorrect index") (absurd <$> rho) | rho <- rhos]
                in case firstJust syntacticMatch rhos' of
                    Nothing -> throwWithMarker (MismatchedAssume asm phi)
                    Just match -> pure (match : goals')
            phi -> throwWithMarker (MismatchedAssume asm phi)

    where
        syntacticMatch :: Formula -> Maybe Formula
        syntacticMatch = \case
            (phi1 `And` phi2) `Implies` psi  | phi1 == asm ->
                Just (phi2 `Implies` psi)
            (phi1 `And` phi2) `Implies` psi  | phi2 == asm ->
                Just (phi1 `Implies` psi)
            phi `Implies` psi  | phi == asm ->
                Just psi
            phi `Or` psi | phi == asm ->
                Just (dual psi)
            _ -> Nothing


checkAbbr :: Abbreviation -> Checking
checkAbbr (Abbreviation symbol scope) = do
    scope' <- transverseScope unabbreviate scope
    modify (\st -> st{checkingAbbreviations = HM.insert symbol scope' (checkingAbbreviations st)})
