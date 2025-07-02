{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Data types for the internal (semantic) syntax tree.
module Syntax.Internal
    ( module Syntax.Internal
    , module Syntax.Abstract
    , module Syntax.LexicalPhrase
    , module Syntax.Token
    ) where


import Base
import Syntax.Lexicon (pattern PairSymbol, pattern ConsSymbol)
import Syntax.LexicalPhrase (LexicalPhrase, SgPl(..), unsafeReadPhrase, unsafeReadPhraseSgPl)
import Syntax.Token (Token(..))

import Syntax.Abstract
    ( Chain(..)
    , Connective(..)
    , VarSymbol(..)
    , FunctionSymbol
    , RelationSymbol
    , StructSymbol (..)
    , Relation
    , VarSymbol(..)
    , PropositionalConstant(..)
    , StructPhrase
    , Justification(..)
    , Marker(..)
    , pattern CarrierSymbol, pattern ConsSymbol
    )

import Bound
import Bound.Scope
import Data.Deriving (deriveShow1, deriveEq1, deriveOrd1)
import Data.Hashable.Lifted
import Data.HashMap.Strict qualified as HM
import Data.Maybe
import Data.Set qualified as Set
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Text.Megaparsec.Pos (SourcePos)

-- | 'Symbol's can be used as function and relation symbols.
data Symbol
    = SymbolMixfix FunctionSymbol
    | SymbolFun (SgPl LexicalPhrase)
    | SymbolInteger Int
    | SymbolPredicate Predicate
    deriving (Show, Eq, Ord, Generic, Hashable)


data Predicate
    = PredicateAdj LexicalPhrase
    | PredicateVerb (SgPl LexicalPhrase)
    | PredicateNoun (SgPl LexicalPhrase) -- ^ /@\<...\> is a \<...\>@/.
    | PredicateRelation RelationSymbol
    | PredicateSymbol Text
    | PredicateNounStruct (SgPl LexicalPhrase) -- ^ /@\<...\> is a \<...\>@/.
    deriving (Show, Eq, Ord, Generic, Hashable)


data Quantifier
    = Universally
    | Existentially
    deriving (Show, Eq, Ord, Generic, Hashable)

type Formula = Term
type Term = Expr
type Expr = ExprOf VarSymbol


-- | Internal higher-order expressions.
data ExprOf a
    = TermVar a
    -- ^ Fresh constants disjoint from all user-named identifiers.
    -- These can be used to eliminate higher-order constructs.
    --
    | TermSymbol Symbol [ExprOf a]
    -- ^ Application of a symbol (including function and predicate symbols).
    | TermSymbolStruct StructSymbol (Maybe (ExprOf a))
    --
    | Apply (ExprOf a) (NonEmpty (ExprOf a))
    -- ^ Higher-order application.
    --
    | TermSep VarSymbol (ExprOf a) (Scope () ExprOf a)
    -- ^ Set comprehension using seperation, e.g.: /@{ x ∈ X | P(x) }@/.
    --
    | Iota VarSymbol (Scope () ExprOf a)
    -- ^ Definite descriptor.
    --
    | ReplacePred VarSymbol VarSymbol (ExprOf a) (Scope ReplacementVar ExprOf a)
    -- ^ Replacement for single-valued predicates. The concrete syntax for these
    -- syntactically requires a bounded existential quantifier in the condition:
    --
    -- /@$\\{ y | \\exists x\\in A. P(x,y) \\}$@/
    --
    -- In definitions the single-valuedness of @P@ becomes a proof obligation.
    -- In other cases we could instead add it as constraint
    --
    -- /@$b\\in \\{ y | \\exists x\\in A. P(x,y) \\}$@/
    -- /@iff@/
    -- /@$\\exists x\\in A. P(x,y)$ and $P$ is single valued@/
    --
    --
    | ReplaceFun (NonEmpty (VarSymbol, ExprOf a)) (Scope VarSymbol ExprOf a) (Scope VarSymbol ExprOf a)
    -- ^ Set comprehension using functional replacement,
    -- e.g.: /@{ f(x, y) | x ∈ X; y ∈ Y; P(x, y) }@/.
    -- The list of pairs gives the domains, the integers in the scope point to list indices.
    -- The first scope is the lhs, the optional scope can be used for additional constraints
    -- on the variables (i.e. implicit separation over the product of the domains).
    -- An out-of-bound index is an error, since otherwise replacement becomes unsound.
    --
    | Connected Connective (ExprOf a) (ExprOf a)
    | Lambda (Scope VarSymbol ExprOf a)
    | Quantified Quantifier (Scope VarSymbol ExprOf a)
    | PropositionalConstant PropositionalConstant
    | Not (ExprOf a)
    deriving (Functor, Foldable, Traversable)

data ReplacementVar = ReplacementDomVar | ReplacementRangeVar deriving (Show, Eq, Ord, Generic, Hashable)

makeBound ''ExprOf

deriveShow1 ''ExprOf
deriveEq1   ''ExprOf
deriveOrd1  ''ExprOf

deriving instance Show a => Show (ExprOf a)
deriving instance Eq   a => Eq   (ExprOf a)
deriving instance Ord  a => Ord  (ExprOf a)

deriving instance Generic (ExprOf a)
deriving instance Generic1 ExprOf

deriving instance Hashable1 ExprOf

deriving instance Hashable a =>  Hashable (ExprOf a)


abstractVarSymbol :: VarSymbol -> ExprOf VarSymbol -> Scope VarSymbol ExprOf VarSymbol
abstractVarSymbol x = abstract (\y -> if x == y then Just x else Nothing)

abstractVarSymbols :: Foldable t => t VarSymbol -> ExprOf VarSymbol -> Scope VarSymbol ExprOf VarSymbol
abstractVarSymbols xs = abstract (\y -> if y `elem` xs then Just y else Nothing)

-- | Use the given set of in scope structures to cast them to their carriers
-- when occurring on the rhs of the element relation.
-- Use the given 'Map' to annotate (unannotated) structure operations
-- with the most recent inscope appropriate label.
annotateWith :: Set VarSymbol -> HashMap StructSymbol VarSymbol -> Formula -> Formula
annotateWith = go
    where
        go :: (Ord a) => Set a -> HashMap StructSymbol a -> ExprOf a -> ExprOf a
        go labels ops = \case
            TermSymbolStruct symb Nothing ->
                -- TODO error if symbol is not instantiated, but only in theorems?
                TermSymbolStruct symb (TermVar <$> HM.lookup symb ops)
            e@TermSymbolStruct{} ->
                e
            a `IsElementOf` TermVar x | x `Set.member` labels ->
                go labels ops a `IsElementOf` TermSymbolStruct CarrierSymbol (Just (TermVar x))
            Not a ->
                Not (go labels ops a)
            Connected conn a b ->
                Connected conn (go labels ops a) (go labels ops b)
            Quantified quant body ->
                Quantified quant (toScope (go (Set.map F labels) (F <$> ops) (fromScope body)))
            e@TermVar{} -> e
            TermSymbol symb args ->
                TermSymbol symb (go labels ops <$> args)
            Apply e1 args ->
                Apply (go labels ops e1) (go labels ops <$> args)
            TermSep vs e scope ->
                TermSep vs (go labels ops e) (toScope (go (Set.map F labels) (F <$> ops) (fromScope scope)))
            Iota x body ->
                Iota x (toScope (go (Set.map F labels) (F <$> ops) (fromScope body)))
            ReplacePred y x xB scope ->
                ReplacePred y x (go labels ops xB) (toScope (go (Set.map F labels) (F <$> ops) (fromScope scope)))
            ReplaceFun bounds ap cond ->
                ReplaceFun
                    (fmap (\(x, e) -> (x, go labels ops e)) bounds)
                    (toScope (go (Set.map F labels) (F <$> ops) (fromScope ap)))
                    (toScope (go (Set.map F labels) (F <$> ops) (fromScope cond)))
            Lambda body ->
                Lambda (toScope (go (Set.map F labels) (F <$> ops) (fromScope body)))
            e@PropositionalConstant{} -> e

containsHigherOrderConstructs :: ExprOf a -> Bool
containsHigherOrderConstructs = \case
    TermSep {} -> True
    Iota{} -> True
    ReplacePred{}-> True
    ReplaceFun{}-> True
    Lambda{} -> True
    Apply{} -> False -- FIXME: this is a lie in general; we need to add sortchecking to determine this.
    TermVar{} -> False
    PropositionalConstant{} -> False
    TermSymbol _ es -> any containsHigherOrderConstructs es
    Not e -> containsHigherOrderConstructs e
    Connected _ e1 e2 -> containsHigherOrderConstructs e1 || containsHigherOrderConstructs e2
    Quantified _ scope -> containsHigherOrderConstructs (fromScope scope)
    TermSymbolStruct _ _ -> False

pattern TermOp :: FunctionSymbol -> [ExprOf a] -> ExprOf a
pattern TermOp op es = TermSymbol (SymbolMixfix op) es

pattern TermConst :: Token -> ExprOf a
pattern TermConst c = TermOp [Just c] []

pattern TermPair :: ExprOf a -> ExprOf a -> ExprOf a
pattern TermPair e1 e2 = TermOp PairSymbol [e1, e2]

pattern Atomic :: Predicate -> [ExprOf a] -> ExprOf a
pattern Atomic symbol args = TermSymbol (SymbolPredicate symbol) args


pattern FormulaAdj :: ExprOf a -> LexicalPhrase -> [ExprOf a] -> ExprOf a
pattern FormulaAdj e adj es = Atomic (PredicateAdj adj) (e:es)

pattern FormulaVerb :: ExprOf a -> SgPl LexicalPhrase -> [ExprOf a] -> ExprOf a
pattern FormulaVerb e verb es = Atomic (PredicateVerb verb) (e:es)

pattern FormulaNoun :: ExprOf a -> SgPl LexicalPhrase -> [ExprOf a] -> ExprOf a
pattern FormulaNoun e noun es = Atomic (PredicateNoun noun) (e:es)

relationNoun :: Expr -> Formula
relationNoun arg = FormulaNoun arg (unsafeReadPhraseSgPl "relation[/s]") []

rightUniqueAdj :: Expr -> Formula
rightUniqueAdj arg = FormulaAdj arg (unsafeReadPhrase "right-unique") []

-- | Untyped quantification.
pattern Forall, Exists :: Scope VarSymbol ExprOf a -> ExprOf a
pattern Forall scope = Quantified Universally  scope
pattern Exists scope = Quantified Existentially scope

makeForall, makeExists :: Foldable t => t VarSymbol -> Formula -> Formula
makeForall xs e = Quantified Universally (abstractVarSymbols xs e)
makeExists xs e = Quantified Existentially (abstractVarSymbols xs e)

instantiateSome :: NonEmpty VarSymbol -> Scope VarSymbol ExprOf VarSymbol -> Scope VarSymbol ExprOf VarSymbol
instantiateSome xs scope = toScope (instantiateEither inst scope)
    where
        inst (Left x) | x `elem` xs = TermVar (F x)
        inst (Left b) = TermVar (B b)
        inst (Right fv) = TermVar (F fv)

-- | Bind all free variables not occuring in the given set universally
forallClosure :: Set VarSymbol -> Formula -> Formula
forallClosure xs phi = if isClosed phi
    then phi
    else Quantified Universally (abstract isNamedVar phi)
        where
            isNamedVar :: VarSymbol -> Maybe VarSymbol
            isNamedVar x = if x `Set.member` xs then Nothing else Just x

freeVars :: ExprOf VarSymbol -> Set VarSymbol
freeVars = Set.fromList . toList

pattern And :: ExprOf a -> ExprOf a -> ExprOf a
pattern And e1 e2 = Connected Conjunction e1 e2

pattern Or :: ExprOf a -> ExprOf a -> ExprOf a
pattern Or e1 e2 = Connected Disjunction e1 e2

pattern Implies :: ExprOf a -> ExprOf a -> ExprOf a
pattern Implies e1 e2 = Connected Implication e1 e2

pattern Iff :: ExprOf a -> ExprOf a -> ExprOf a
pattern Iff e1 e2 = Connected Equivalence e1 e2

pattern Xor :: ExprOf a -> ExprOf a -> ExprOf a
pattern Xor e1 e2 = Connected ExclusiveOr e1 e2


pattern Bottom :: ExprOf a
pattern Bottom = PropositionalConstant IsBottom

pattern Top :: ExprOf a
pattern Top = PropositionalConstant IsTop


pattern Relation :: RelationSymbol -> [ExprOf a] -> ExprOf a
pattern Relation rel es = Atomic (PredicateRelation rel) es

-- | Membership.
pattern IsElementOf :: ExprOf a -> ExprOf a -> ExprOf a
pattern IsElementOf e1 e2 = Atomic (PredicateRelation (Command "in")) (e1 : [e2])

-- | Membership.
pattern IsNotElementOf :: ExprOf a -> ExprOf a -> ExprOf a
pattern IsNotElementOf e1 e2 = Not (IsElementOf e1 e2)

-- | Subset relation (non-strict).
pattern IsSubsetOf :: ExprOf a -> ExprOf a -> ExprOf a
pattern IsSubsetOf e1 e2 = Atomic (PredicateRelation (Command "subseteq")) (e1 : [e2])

-- | Ordinal predicate.
pattern IsOrd :: ExprOf a -> ExprOf a
pattern IsOrd e1 = Atomic (PredicateNoun (SgPl [Just "ordinal"] [Just "ordinals"])) [e1]

-- | Equality.
pattern Equals :: ExprOf a -> ExprOf a -> ExprOf a
pattern Equals e1 e2 = Atomic (PredicateRelation (Symbol "=")) (e1 : [e2])

-- | Disequality.
pattern NotEquals :: ExprOf a -> ExprOf a -> ExprOf a
pattern NotEquals e1 e2 = Atomic (PredicateRelation (Command "neq")) (e1 : [e2])

pattern EmptySet :: ExprOf a
pattern EmptySet = TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []

makeConjunction :: [ExprOf a] -> ExprOf a
makeConjunction = \case
    [] -> Top
    es -> List.foldl1' And es

makeDisjunction :: [ExprOf a] -> ExprOf a
makeDisjunction = \case
    [] -> Bottom
    es -> List.foldl1' Or es

makeIff :: [ExprOf a] -> ExprOf a
makeIff = \case
    [] -> Bottom
    es -> List.foldl1' Iff es
    
makeXor :: [ExprOf a] -> ExprOf a
makeXor = \case
    [] -> Bottom
    es -> List.foldl1' Xor es

finiteSet :: NonEmpty (ExprOf a) -> ExprOf a
finiteSet = foldr cons EmptySet
    where
        cons x y = TermSymbol (SymbolMixfix ConsSymbol) [x, y]

isPositive :: ExprOf a -> Bool
isPositive = \case
    Not _ -> False
    _ -> True

dual :: ExprOf a -> ExprOf a
dual = \case
    Not f -> f
    f -> Not f



-- | Local assumptions.
data Asm
    = Asm Formula
    | AsmStruct VarSymbol StructPhrase


deriving instance Show Asm
deriving instance Eq   Asm
deriving instance Ord  Asm

data StructAsm
    = StructAsm VarSymbol StructPhrase



data Axiom = Axiom [Asm] Formula

deriving instance Show Axiom
deriving instance Eq   Axiom
deriving instance Ord  Axiom


data Lemma = Lemma [Asm] Formula

deriving instance Show Lemma
deriving instance Eq   Lemma
deriving instance Ord  Lemma


data Defn
    = DefnPredicate [Asm] Predicate (NonEmpty VarSymbol) Formula
    | DefnFun [Asm] (SgPl LexicalPhrase) [VarSymbol] Term
    | DefnOp FunctionSymbol [VarSymbol] Term

deriving instance Show Defn
deriving instance Eq   Defn
deriving instance Ord  Defn

data Inductive = Inductive
    { inductiveSymbol :: FunctionSymbol
    , inductiveParams :: [VarSymbol]
    , inductiveDomain :: Expr
    , inductiveIntros :: NonEmpty IntroRule
    }
    deriving (Show, Eq, Ord)

data IntroRule = IntroRule
    { introConditions :: [Formula] -- The inductively defined set may only appear as an argument of monotone operations on the rhs.
    , introResult :: Formula -- TODO Refine.
    }
    deriving (Show, Eq, Ord)


data Proof
    = Omitted
    -- ^ Ends a proof without further verification.
    -- This results in a “gap” in the formalization.
    | Qed Justification
    -- ^ Ends of a proof, leaving automation to discharge the current goal using the given justification.
    | ByContradiction Proof
    -- ^ Take the dual of the current goal as an assumption and
    -- set the goal to absurdity.
    | BySetInduction (Maybe Term) Proof
    -- ^ ∈-induction.
    | ByOrdInduction Proof
    -- ^ Transfinite induction for ordinals.
    | Assume Formula Proof
    -- ^ Simplify goals that are implications or disjunctions.
    | Fix (NonEmpty VarSymbol) Formula Proof
    -- ^ Simplify universal goals (with an optional bound or such that statement)
    | Take (NonEmpty VarSymbol) Formula Justification Proof
    -- ^ Use existential assumptions.
    | Suffices Formula Justification Proof
    | ByCase [Case]
    -- ^ Proof by case. Disjunction of the case hypotheses 'Case'
    -- must hold for this step to succeed. Each case starts a subproof,
    -- keeping the same goal but adding the case hypothesis as an assumption.
    -- Often this will be a classical split between /@P@/ and /@not P@/, in
    -- which case the proof that /@P or not P@/ holds is easy.
    --
    | Have Formula Justification Proof
    -- ^ An affirmation, e.g.: /@We have \<stmt\> by \<ref\>@/.
    --
    | Calc Calc Proof
    | Subclaim Formula Proof Proof
    -- ^ A claim is a sublemma with its own proof:
    --
    -- /@Show \<goal stmt\>. \<steps\>. \<continue other proof\>.@/
    --
    -- A successful first proof adds the claimed formula as an assumption
    -- for the remaining proof.
    --
    | Define VarSymbol Term Proof
    | DefineFunction VarSymbol VarSymbol Term Term Proof

    | DefineFunctionLocal VarSymbol VarSymbol VarSymbol Term (NonEmpty (Term, Formula)) Proof

deriving instance Show Proof
deriving instance Eq   Proof
deriving instance Ord  Proof



-- | A case of a case split.
data Case = Case
    { caseOf :: Formula
    , caseProof :: Proof
    }

deriving instance Show Case
deriving instance Eq   Case
deriving instance Ord  Case

-- | See 'Syntax.Abstract.Calc'.
data Calc
    = Equation Term (NonEmpty (Term, Justification))
    | Biconditionals Term (NonEmpty (Term, Justification))

deriving instance Show Calc
deriving instance Eq   Calc
deriving instance Ord  Calc

calcResult :: Calc -> ExprOf VarSymbol
calcResult = \case
    Equation e eqns -> e `Equals` fst (NonEmpty.last eqns)
    Biconditionals phi phis -> phi `Iff` fst (NonEmpty.last phis)

calculation :: Calc -> [(ExprOf VarSymbol, Justification)]
calculation = \case
    Equation e1 eqns@((e2, jst) :| _) -> (e1 `Equals` e2, jst) : collectEquations (toList eqns)
    Biconditionals p1 ps@((p2, jst) :| _) -> (p1 `Iff` p2, jst) : collectBiconditionals (toList ps)


collectEquations :: [(ExprOf a, b)] -> [(ExprOf a, b)]
collectEquations = \case
    (e1, _) : eqns'@((e2, jst) : _) -> (e1 `Equals` e2, jst) : collectEquations eqns'
    _ -> []

collectBiconditionals :: [(ExprOf a, b)] -> [(ExprOf a, b)]
collectBiconditionals = \case
    (p1, _) : ps@((p2, jst) : _) -> (p1 `Iff` p2, jst) : collectEquations ps
    _ -> []


newtype Datatype
    = DatatypeFin (NonEmpty Text)
    deriving (Show, Eq, Ord)


data Signature
    = SignaturePredicate Predicate (NonEmpty VarSymbol)
    | SignatureFormula Formula -- TODO: Reconsider, this is pretty lossy.

deriving instance Show Signature
deriving instance Eq   Signature
deriving instance Ord  Signature

data StructDefn = StructDefn
    { structPhrase :: StructPhrase
    -- ^ The noun phrase naming the structure, e.g.: @partial order@ or @abelian group@.
    , structParents :: Set StructPhrase
    , structDefnLabel :: VarSymbol
    , structDefnFixes :: Set StructSymbol
    -- ^ List of commands representing operations,
    -- e.g.: @\\contained@ or @\\inv@. These are used as default operation names
    -- in instantiations such as @Let $G$ be a group@.
    -- The commands should be set up to handle an optional struct label
    -- which would typically be rendered as a sub- or superscript, e.g.:
    -- @\\contained[A]@ could render as ”⊑ᴬ“.
    --    --
    , structDefnAssumes :: [(Marker, Formula)]
    -- ^ The assumption or axioms of the structure.
    -- To be instantiate with the @structFixes@ of a given structure.
    }

deriving instance Show StructDefn
deriving instance Eq   StructDefn
deriving instance Ord  StructDefn


data Abbreviation
    = Abbreviation Symbol (Scope Int ExprOf Void)
    deriving (Show, Eq, Ord)

data Block
    = BlockAxiom SourcePos Marker Axiom
    | BlockLemma SourcePos Marker Lemma
    | BlockProof SourcePos Proof
    | BlockDefn SourcePos Marker Defn
    | BlockAbbr SourcePos Marker Abbreviation
    | BlockStruct SourcePos Marker StructDefn
    | BlockInductive SourcePos Marker Inductive
    | BlockSig SourcePos [Asm] Signature
    deriving (Show, Eq, Ord)


data Task = Task
    { taskDirectness :: Directness
    , taskHypotheses :: [(Marker, Formula)] -- ^ No guarantees on order.
    , taskConjectureLabel :: Marker
    , taskConjecture :: Formula
    } deriving (Show, Eq, Generic, Hashable)


-- | Indicates whether a given proof is direct or indirect.
-- An indirect proof (i.e. a proof by contradiction) may
-- cause an ATP to emit a warning about contradictory axioms.
-- When we know that the proof is indirect, we want to ignore
-- this warning. For relevance filtering we also want to know
-- what our actual goal is, so we keep the original conjecture.
data Directness
    = Indirect Formula -- ^ The former conjecture.
    | Direct
    deriving (Show, Eq, Generic, Hashable)

isIndirect :: Task -> Bool
isIndirect task = case taskDirectness task of
    Indirect _ -> True
    Direct -> False


-- | Boolean contraction of a task.
contractionTask :: Task -> Task
contractionTask task = task
    { taskHypotheses = mapMaybe contract (taskHypotheses task)
    , taskConjecture = contraction (taskConjecture task)
    }

contract :: (Marker, Formula) -> Maybe (Marker, Formula)
contract (m, phi) = case contraction phi of
    Top -> Nothing
    phi' -> Just (m, phi')



-- | Full boolean contraction.
contraction :: ExprOf a -> ExprOf a
contraction = \case
    Connected conn f1 f2  -> atomicContraction (Connected conn (contraction f1) (contraction f2))
    Quantified quant scope -> atomicContraction (Quantified quant (hoistScope contraction scope))
    Not f -> Not (contraction f)
    f -> f


-- | Atomic boolean contraction.
atomicContraction :: ExprOf a -> ExprOf a
atomicContraction = \case
    Top    `Iff` f      -> f
    Bottom `Iff` f      -> Not f
    f      `Iff` Top    -> f
    f      `Iff` Bottom -> Not f

    Top    `Implies` f      -> f
    Bottom `Implies` _      -> Top
    _      `Implies` Top    -> Top
    f      `Implies` Bottom -> Not f

    Top    `And` f      -> f
    Bottom `And` _      -> Bottom
    f      `And` Top    -> f
    _      `And` Bottom -> Bottom

    phi@(Quantified _quant scope) -> case unscope scope of
        Top -> Top
        Bottom -> Bottom
        _ -> phi

    Not Top    -> Bottom
    Not Bottom -> Top

    f -> f
