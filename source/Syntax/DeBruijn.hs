{-# LANGUAGE DeriveAnyClass #-}

module Syntax.DeBruijn
    ( module Syntax.DeBruijn
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
    , PropositionalConstant(..)
    , StructPhrase
    , Justification(..)
    , Marker(..)
    , pattern CarrierSymbol, pattern ConsSymbol, pattern ElementSymbol
    )

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Text.Megaparsec.Pos (SourcePos)

-- | 'Symbol' defined at the top level.
data Symbol
    = SymbolMixfix FunctionSymbol
    | SymbolFun (SgPl LexicalPhrase)
    | SymbolInteger Int
    | SymbolPredicate Predicate
    deriving (Show, Eq, Ord, Generic, Hashable)

-- | Predicate symbols.
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

-- | Internal high-order expression, using variables with scoped de Bruijn indices.
data Expr
    = Var {name :: VarSymbol, index :: Int}
    -- ^ Indexed variables
    | TermSymbol Symbol [Expr]
    -- ^ Direct application of a symbol, in particular first-order function and predicate symbols.
    | TermSymbolStruct StructSymbol (Maybe Expr)
    -- ^ Structure symbol with an optional label.
    | Replacement Replacement
    | Apply Expr Expr
    -- ^ Higher-order application.
    | PropositionalConstant PropositionalConstant
    | Not Expr
    | Connected Connective Expr Expr
    | Lambda VarSymbol Expr
    | Quantified Quantifier VarSymbol Expr
    deriving (Show, Eq, Ord, Generic, Hashable)

type Formula = Expr
type Term = Expr

-- | A set comprehension that is a replacement expression with side conditions.
-- They look like @{ f(x,y,z) | x\\in X, y\\in Y(x), z\\in Z(x,y) | \\phi(x,y,z) }@, where
--
--  1. @f(x,y,z)@ is the replacement value with bound variables @x,y,z@
--
--  2. @x\\in X@, @y\\in Y(x)@, etc. are the replacement bindings with their domains (which may depend on earlier bound variables)
--
--  3. @\\phi(x,y,z)@ is the optional replacement condition
--
-- The case of no replacement condition is represented by using the constant @Top@ as the formula.
-- Bound variables scope over inner (later) bindings, the replacement value, and the replacement condition.
-- Similar constructs are sometimes called ReplSep or Fraenkel operator in other systems.
-- The degenerate case of no bindings is allowed, resulting in a subsingleton set (singleton or empty set, depending on if the condition is holds or not).
data Replacement
    = ReplacementBinding {replacementVar :: VarSymbol, replacementDomain :: Expr, replacement :: Replacement}
    | ReplacementBody {replacementValue :: Expr, replacementCondition :: Expr}
    deriving (Show, Eq, Ord, Generic, Hashable)

-- | Increase the index of all free variables matching the given variable name
shift
    :: Int
    -- ^ The amount to shift by
    -> VarSymbol
    -- ^ The variable name to match
    -> Int
    -- ^ The minimum index of variables to match
    -> Expr
    -- ^ The expression to shift
    -> Expr
shift offset y = go
    where
    go minIndex = \case
        Var x i ->
            let i' = if x == y && minIndex <= i then i + offset else i
            in Var x i'
        Lambda x body ->
            let minIndex' = if x == y then minIndex + 1 else minIndex
                body' = go minIndex' body
            in Lambda x body'
        Quantified q x body ->
            let minIndex' = if x == y then minIndex + 1 else minIndex
                body' = go minIndex' body
            in Quantified q x body'
        Replacement repl -> Replacement (shiftReplacement offset y minIndex repl)
        Apply f a ->
            Apply (go minIndex f) (go minIndex a)
        TermSymbol s args ->
            TermSymbol s (map (go minIndex) args)
        TermSymbolStruct s me ->
            TermSymbolStruct s (fmap (go minIndex) me)
        PropositionalConstant c -> PropositionalConstant c
        Not e -> Not (go minIndex e)
        Connected c e1 e2 -> Connected c (go minIndex e1) (go minIndex e2)


shiftReplacement
    :: Int
    -> VarSymbol
    -> Int
    -> Replacement
    -> Replacement
shiftReplacement offset y = go where
    go minIndex (ReplacementBody value cond) =
        ReplacementBody (shift offset y minIndex value) (shift offset y minIndex cond)
    go minIndex (ReplacementBinding x domain repl) =
        let domain' = shift offset y minIndex domain -- The variable is not bound in its domain, so use the current minIndex
            minIndex' = if x == y then minIndex + 1 else minIndex
            repl' = go minIndex' repl
        in  ReplacementBinding x domain' repl'

-- | Substitute all free occurrences of a variable with given name and index with a new expression.
substitute
    :: VarSymbol -- ^ Target variable name
    -> Int -- ^ Target variable index
    -> Expr -- ^ New expression to substitute
    -> Expr -- ^ Expression to perform substitution in
    -> Expr
substitute targetName targetIndex new = go where
    go = \case
        xi@(Var x i) -> if x == targetName && i == targetIndex then new else xi
        Lambda x body ->
            let targetIndex' = if x == targetName then targetIndex + 1 else targetIndex
                newShifted = shift 1 x 0 new
                body' = substitute targetName targetIndex' newShifted body
            in  Lambda x body'
        Quantified q x body ->
            let targetIndex' = if x == targetName then targetIndex + 1 else targetIndex
                newShifted = shift 1 x 0 new
                body' = substitute targetName targetIndex' newShifted body
            in  Quantified q x body'
        Replacement repl -> Replacement (substituteReplacement targetName targetIndex new repl)
        Apply e1 e2 -> Apply (go e1) (go e2)
        TermSymbol sym args -> TermSymbol sym (go <$> args)
        TermSymbolStruct s m -> TermSymbolStruct s (go <$> m)
        PropositionalConstant pc -> PropositionalConstant pc
        Not e -> Not (go e)
        Connected c e1 e2 -> Connected c (go e1) (go e2)


substituteReplacement
    :: VarSymbol -- ^ Target variable name
    -> Int -- ^ Target variable index
    -> Expr  -- ^ New expression to substitute
    -> Replacement -- ^ Replacement expression to perform substitution in
    -> Replacement
substituteReplacement targetName targetIndex new = go
  where
    go (ReplacementBody value cond) =
        ReplacementBody
            (substitute targetName targetIndex new value)
            (substitute targetName targetIndex new cond)
    go (ReplacementBinding x domain repl) =
        let -- The domain is NOT under the scope of the current binder, so we proceed directly
            domain' = substitute targetName targetIndex new domain
            -- For the inner part we shift by 1 relative to new, analogous to other binding constructs
            newShifted = shift 1 x 0 new
            targetIndex' = if x == targetName then targetIndex + 1 else targetIndex
            repl' = substituteReplacement targetName targetIndex' newShifted repl
         in ReplacementBinding x domain' repl'


-- | β-reduce an expression
betaReduce :: Expr -> Expr
betaReduce = \case
        xi@Var{} -> xi
        Lambda x e ->
            Lambda x (betaReduce e)
        Apply function argument ->
            let function' = betaReduce function
                argument' = betaReduce argument
             in case function' of
                    Lambda x e ->
                        let shiftedArgument = shift 1 x 0 argument'
                            substitutedBody = substitute x 0 shiftedArgument e
                            unshiftedBody = shift (-1) x 0 substitutedBody
                            e' = betaReduce unshiftedBody
                         in e'
                    _ -> Apply function' argument'

        TermSymbol sym args ->
            TermSymbol sym (betaReduce <$> args)
        TermSymbolStruct s m ->
            TermSymbolStruct s (betaReduce <$> m)
        Replacement repl ->
            Replacement (betaReduceReplacement repl)
        PropositionalConstant pc -> PropositionalConstant pc
        Not e' -> Not (betaReduce e')
        Connected c l r -> Connected c (betaReduce l) (betaReduce r)
        Quantified q binder e -> Quantified q binder (betaReduce e)

betaReduceReplacement :: Replacement -> Replacement
betaReduceReplacement = \case
    ReplacementBody value cond -> ReplacementBody (betaReduce value) (betaReduce cond)
    ReplacementBinding binder domain repl -> ReplacementBinding binder (betaReduce domain) (betaReduceReplacement repl)

-- | α-reduce an expression, renaming all bound variables to @\_@
alphaReduce :: Expr -> Expr
alphaReduce e0 = let dflt = "_" in case e0 of
    Var vName vIndex -> Var vName vIndex

    Lambda binder e ->
        let shiftedBody = shift 1 dflt 0 e
            substitutedBody = substitute binder 0 (Var dflt 0) shiftedBody
            unshiftedBody = shift (-1) binder 0 substitutedBody
            e' = alphaReduce unshiftedBody
            in Lambda dflt e'

    Quantified q binder e ->
        let shiftedBody = shift 1 dflt 0 e
            substitutedBody = substitute binder 0 (Var dflt 0) shiftedBody
            unshiftedBody = shift (-1) binder 0 substitutedBody
            e' = alphaReduce unshiftedBody
            in Quantified q dflt e'
    Replacement repl -> Replacement (alphaReduceReplacement dflt repl)
    Apply f a -> Apply (alphaReduce f) (alphaReduce a)
    TermSymbol s args -> TermSymbol s (map alphaReduce args)
    TermSymbolStruct s m -> TermSymbolStruct s (fmap alphaReduce m)
    PropositionalConstant pc -> PropositionalConstant pc
    Not e -> Not (alphaReduce e)
    Connected c l r -> Connected c (alphaReduce l) (alphaReduce r)

-- | α-reduce a replacement expression, renaming all bound variables to given default variable name (to be inherited from 'alphaReduce').
alphaReduceReplacement :: VarSymbol -> Replacement -> Replacement
alphaReduceReplacement dflt = \case
    ReplacementBody value cond ->
        ReplacementBody (alphaReduce value) (alphaReduce cond)
    ReplacementBinding binder domain repl ->
        let domain' = alphaReduce domain
            shiftedRepl = shiftReplacement 1 dflt 0 repl
            substitutedRepl = substituteReplacement binder 0 (Var dflt 0) shiftedRepl
            unshiftedRepl = shiftReplacement (-1) binder 0 substitutedRepl
            repl' = alphaReduceReplacement dflt unshiftedRepl
        in  ReplacementBinding dflt domain' repl'


pattern TermOp :: FunctionSymbol -> [Expr] -> Expr
pattern TermOp op es = TermSymbol (SymbolMixfix op) es

pattern TermConst :: Token -> Expr
pattern TermConst c = TermOp [Just c] []

pattern TermPair :: Expr -> Expr -> Expr
pattern TermPair e1 e2 = TermOp PairSymbol [e1, e2]

pattern Atomic :: Predicate -> [Expr] -> Expr
pattern Atomic symbol args = TermSymbol (SymbolPredicate symbol) args

pattern FormulaAdj :: Expr -> LexicalPhrase -> [Expr] -> Expr
pattern FormulaAdj e adj es = Atomic (PredicateAdj adj) (e:es)

pattern FormulaVerb :: Expr -> SgPl LexicalPhrase -> [Expr] -> Expr
pattern FormulaVerb e verb es = Atomic (PredicateVerb verb) (e:es)

pattern FormulaNoun :: Expr -> SgPl LexicalPhrase -> [Expr] -> Expr
pattern FormulaNoun e noun es = Atomic (PredicateNoun noun) (e:es)

relationNoun :: Expr -> Formula
relationNoun arg = FormulaNoun arg (unsafeReadPhraseSgPl "relation[/s]") []

rightUniqueAdj :: Expr -> Formula
rightUniqueAdj arg = FormulaAdj arg (unsafeReadPhrase "right-unique") []

-- | Untyped quantification.
pattern Forall, Exists :: VarSymbol -> Expr -> Expr
pattern Forall x body = Quantified Universally x body
pattern Exists x body = Quantified Existentially x body

makeForall, makeExists :: Foldable t => t VarSymbol -> Formula -> Formula
makeForall xs e = foldr Forall e xs
makeExists xs e = foldr Exists e xs


freeVars :: Expr -> Set VarSymbol
freeVars = freeVarsWith Map.empty

freeVarsWith :: Map VarSymbol Int -> Expr -> Set VarSymbol
freeVarsWith counts = \case
        Var x i ->
            let current = Map.findWithDefault 0 x counts
            in  if i >= current then Set.singleton x else Set.empty
        Lambda binder body ->
            let counts' = Map.insertWith (+) binder 1 counts
            in  freeVarsWith counts' body
        Quantified _ binder body ->
            let counts' = Map.insertWith (+) binder 1 counts
            in  freeVarsWith counts' body
        Apply e1 e2 ->
            Set.union (freeVarsWith counts e1) (freeVarsWith counts e2)
        Replacement repl -> freeVarsReplacementWith counts repl
        TermSymbol _s args ->
            List.foldl' (\acc e -> Set.union acc (freeVarsWith counts e)) Set.empty args
        TermSymbolStruct _s me ->
            maybe Set.empty (freeVarsWith counts) me
        PropositionalConstant _ -> Set.empty
        Not e -> freeVarsWith counts e
        Connected _ e1 e2 ->
            Set.union (freeVarsWith counts e1) (freeVarsWith counts e2)

freeVarsReplacement :: Replacement -> Set VarSymbol
freeVarsReplacement = freeVarsReplacementWith Map.empty

freeVarsReplacementWith :: Map VarSymbol Int -> Replacement -> Set VarSymbol
freeVarsReplacementWith counts = \case
    ReplacementBody value cond ->
        Set.union (freeVarsWith counts value) (freeVarsWith counts cond)
    ReplacementBinding binder domain rest ->
        let fvDomain = freeVarsWith counts domain
            counts'  = Map.insertWith (+) binder 1 counts
            fvRest   = freeVarsReplacementWith counts' rest
        in  Set.union fvDomain fvRest


pattern And :: Expr -> Expr -> Expr
pattern And e1 e2 = Connected Conjunction e1 e2

pattern Or :: Expr -> Expr -> Expr
pattern Or e1 e2 = Connected Disjunction e1 e2

pattern Implies :: Expr -> Expr -> Expr
pattern Implies e1 e2 = Connected Implication e1 e2

pattern Iff :: Expr -> Expr -> Expr
pattern Iff e1 e2 = Connected Equivalence e1 e2

pattern Xor :: Expr -> Expr -> Expr
pattern Xor e1 e2 = Connected ExclusiveOr e1 e2

pattern Bottom :: Expr
pattern Bottom = PropositionalConstant IsBottom

pattern Top :: Expr
pattern Top = PropositionalConstant IsTop

pattern Relation :: RelationSymbol -> [Expr] -> Expr
pattern Relation rel es = Atomic (PredicateRelation rel) es

-- | Set membership.
pattern IsElementOf, IsNotElementOf :: Expr -> Expr -> Expr
pattern IsElementOf e1 e2 = Atomic (PredicateRelation ElementSymbol) (e1 : [e2])
pattern IsNotElementOf e1 e2 = Not (IsElementOf e1 e2)

-- | Subset relation (non-strict).
pattern IsSubsetOf :: Expr -> Expr -> Expr
pattern IsSubsetOf e1 e2 = Atomic (PredicateRelation (Command "subseteq")) (e1 : [e2])

-- | Ordinal predicate.
pattern IsOrd :: Expr -> Expr
pattern IsOrd e1 = Atomic (PredicateNoun (SgPl [Just "ordinal"] [Just "ordinals"])) [e1]

-- | First-order equality.
pattern Equals :: Expr -> Expr -> Expr
pattern Equals e1 e2 = Atomic (PredicateRelation (Symbol "=")) (e1 : [e2])

-- | First-order disequality.
pattern NotEquals :: Expr -> Expr -> Expr
pattern NotEquals e1 e2 = Atomic (PredicateRelation (Command "neq")) (e1 : [e2])

pattern EmptySet :: Expr
pattern EmptySet = TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []

makeConjunction :: [Expr] -> Expr
makeConjunction = \case
    [] -> Top
    es -> List.foldl1' (\a b -> And a b) es

makeDisjunction :: [Expr] -> Expr
makeDisjunction = \case
    [] -> Bottom
    es -> List.foldl1' (\a b -> Or a b) es

makeIff :: [Expr] -> Expr
makeIff = \case
    [] -> Bottom
    es -> List.foldl1' (\a b -> Iff a b) es

makeXor :: [Expr] -> Expr
makeXor = \case
    [] -> Bottom
    es -> List.foldl1' (\a b -> Xor a b) es

finiteSet :: NonEmpty Expr -> Expr
finiteSet = foldr cons EmptySet where
    cons x y = TermSymbol (SymbolMixfix ConsSymbol) [x, y]

isPositive :: Expr -> Bool
isPositive = \case
    Not _ -> False
    _ -> True

dual :: Expr -> Expr
dual = \case
    Not f -> f
    f -> Not f



data Asm
    = Asm Formula
    | AsmStruct VarSymbol StructPhrase
    deriving (Show, Eq, Ord)

data StructAsm = StructAsm VarSymbol StructPhrase deriving (Show, Eq, Ord)

data Axiom = Axiom [Asm] Formula deriving (Show, Eq, Ord)

data Lemma = Lemma [Asm] Formula deriving (Show, Eq, Ord)


data Defn
    = DefnPredicate [Asm] Predicate (NonEmpty VarSymbol) Formula
    | DefnFun [Asm] (SgPl LexicalPhrase) [VarSymbol] Term
    | DefnOp FunctionSymbol [VarSymbol] Term
    deriving (Show, Eq, Ord)


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

data CalcQuantifier
    = CalcForall (NonEmpty VarSymbol) (Maybe Formula)
    | CalcUnquantified
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
    | Calc CalcQuantifier Calc Proof
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
    deriving (Show, Eq, Ord)

-- | An individual case in a case split.
data Case = Case
    { caseOf :: Formula
    , caseProof :: Proof
    } deriving (Show, Eq, Ord)

-- | See 'Syntax.Abstract.Calc'.
data Calc
    = Equation Term (NonEmpty (Term, Justification))
    | Biconditionals Term (NonEmpty (Term, Justification))
    deriving (Show, Eq, Ord)

calcQuant :: CalcQuantifier -> (Formula -> Formula)
calcQuant = \case
    CalcUnquantified -> id
    CalcForall xs maySuchThat -> case maySuchThat of
        Nothing -> makeForall xs
        Just suchThat -> \phi -> makeForall xs (suchThat `Implies` phi)

calcResult :: CalcQuantifier -> Calc -> Expr
calcResult quant = \case
    Equation e eqns -> calcQuant quant (e `Equals` fst (NonEmpty.last eqns))
    Biconditionals phi phis -> calcQuant quant (phi `Iff` fst (NonEmpty.last phis))

calculation :: CalcQuantifier -> Calc -> [(Expr, Justification)]
calculation quant = \case
    Equation e1 eqns@((e2, jst) :| _) -> (calcQuant quant (e1 `Equals` e2), jst) : collectEquations quant (toList eqns)
    Biconditionals p1 ps@((p2, jst) :| _) -> (calcQuant quant (p1 `Iff` p2), jst) : collectBiconditionals quant (toList ps)


collectEquations :: CalcQuantifier -> [(Formula, j)] -> [(Formula, j)]
collectEquations quant = \case
    (e1, _) : eqns'@((e2, jst) : _) -> (calcQuant quant (e1 `Equals` e2), jst) : collectEquations quant eqns'
    _ -> []

collectBiconditionals :: CalcQuantifier -> [(Formula, j)] -> [(Formula, j)]
collectBiconditionals quant = \case
    (p1, _) : ps@((p2, jst) : _) -> (calcQuant quant (p1 `Iff` p2), jst) : collectBiconditionals quant ps
    _ -> []


newtype Datatype = DatatypeFin (NonEmpty Text) deriving (Show, Eq, Ord)

data Signature
    = SignaturePredicate Predicate (NonEmpty VarSymbol)
    | SignatureFormula Formula -- LATER: Reconsider, this is pretty lossy.
    deriving (Show, Eq, Ord)

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
    } deriving (Show, Eq, Ord)

data Abbreviation
    = Abbreviation Symbol Expr
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
contraction :: Expr -> Expr
contraction = \case
    Connected conn f1 f2  -> atomicContraction (Connected conn (contraction f1) (contraction f2))
    Quantified quant x body -> atomicContraction (Quantified quant x (contraction body))
    Not f -> Not (contraction f)
    f -> f


-- | Atomic boolean contraction.
atomicContraction :: Expr-> Expr
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

    phi@(Quantified _quant _ body) -> case body of
        Top -> Top
        Bottom -> Bottom
        _ -> phi

    Not Top    -> Bottom
    Not Bottom -> Top

    f -> f
