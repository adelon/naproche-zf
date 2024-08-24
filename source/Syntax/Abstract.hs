{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}


-- | Data types for the abstract syntax tree and helper functions
-- for constructing the lexicon.
--
module Syntax.Abstract
    ( module Syntax.Abstract
    , module Syntax.LexicalPhrase
    , module Syntax.Token
    ) where


import Base
import Syntax.LexicalPhrase (LexicalPhrase, SgPl(..), unsafeReadPhraseSgPl, unsafeReadPhrase)
import Syntax.Token (Token(..))

import Text.Earley.Mixfix (Holey)
import Data.Text qualified as Text
import Text.Megaparsec.Pos (SourcePos)

-- | Local "variable-like" symbols that can be captured by binders.
data VarSymbol
    = NamedVar Text -- ^ A named variable.
    | FreshVar Int -- ^ A nameless (implicit) variable. Should only come from desugaring.
    deriving (Show, Eq, Ord, Generic, Hashable)

instance IsString VarSymbol where
    fromString v = NamedVar $ Text.pack v


data Expr
    = ExprVar VarSymbol
    | ExprInteger Int
    | ExprOp FunctionSymbol [Expr]
    | ExprStructOp StructSymbol (Maybe Expr)
    | ExprFiniteSet (NonEmpty Expr)
    | ExprSep VarSymbol Expr Stmt
    -- ^ Of the form /@{x ∈ X | P(x)}@/.
    | ExprReplace Expr (NonEmpty (VarSymbol,Expr)) (Maybe Stmt)
    -- ^ E.g.: /@{ f(x, y) | x ∈ X, y ∈ Y | P(x, y) }@/.
    | ExprReplacePred VarSymbol VarSymbol Expr Stmt
    -- ^ E.g.: /@{ y | \\exists x\\in X. P(x, y) }@/.
    deriving (Show, Eq, Ord)


type FunctionSymbol = Holey Token

type RelationSymbol = Token

newtype StructSymbol = StructSymbol { unStructSymbol :: Text } deriving newtype (Show, Eq, Ord, Hashable)

-- | The predefined @cons@ function symbol used for desugaring finite set expressions.
pattern ConsSymbol :: FunctionSymbol
pattern ConsSymbol = [Just (Command "cons"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]

-- | The predefined @pair@ function symbol used for desugaring tuple notation..
pattern PairSymbol :: FunctionSymbol
pattern PairSymbol = [Just (Command "pair"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]

-- | Function application /@f(x)@/ desugars to /@\apply{f}{x}@/.
pattern ApplySymbol :: FunctionSymbol
pattern ApplySymbol = [Just (Command "apply"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]

pattern DomSymbol :: FunctionSymbol
pattern DomSymbol = [Just (Command "dom"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]

pattern CarrierSymbol :: StructSymbol
pattern CarrierSymbol = StructSymbol "carrier"

pattern ExprConst :: Token -> Expr
pattern ExprConst c = ExprOp [Just c] []

pattern ExprApp :: Expr -> Expr -> Expr
pattern ExprApp e1 e2 = ExprOp ApplySymbol [e1, e2]

pattern ExprPair :: Expr -> Expr -> Expr
pattern ExprPair e1 e2 = ExprOp PairSymbol [e1, e2]

-- | Tuples are interpreted as nested pairs:
-- the triple /@(a, b, c)@/ is interpreted as
-- /@(a, (b, c))@/.
-- This means that the product operation should also
-- be right associative, so that /@(a, b, c)@/ can
-- form elements of /@A\times B\times C@/.
makeTuple :: NonEmpty Expr -> Expr
makeTuple = foldr1 ExprPair


data Chain
    = ChainBase (NonEmpty Expr) Sign Relation (NonEmpty Expr)
    | ChainCons (NonEmpty Expr) Sign Relation Chain
    deriving (Show, Eq, Ord)

data Relation
    = RelationSymbol RelationSymbol  -- ^  E.g.: /@x \in X@/
    | RelationExpr Expr   -- ^  E.g.: /@x \mathrel{R} y@/
    deriving (Show, Eq, Ord)

data Sign = Positive | Negative deriving (Show, Eq, Ord)

data Formula
    = FormulaChain Chain
    | FormulaPredicate PrefixPredicate (NonEmpty Expr)
    | Connected Connective Formula Formula
    | FormulaNeg Formula
    | FormulaQuantified Quantifier (NonEmpty VarSymbol) Bound Formula
    | PropositionalConstant PropositionalConstant
    deriving (Show, Eq, Ord)

data PropositionalConstant = IsBottom | IsTop
    deriving (Show, Eq, Ord, Generic, Hashable)

data PrefixPredicate
    = PrefixPredicate Text Int
    deriving (Show, Eq, Ord, Generic, Hashable)


data Connective
    = Conjunction
    | Disjunction
    | Implication
    | Equivalence
    | ExclusiveOr
    | NegatedDisjunction
    deriving (Show, Eq, Ord, Generic, Hashable)



makeConnective :: Holey Token -> [Formula] -> Formula
makeConnective [Nothing, Just (Command "implies"), Nothing] [f1, f2] = Connected Implication  f1 f2
makeConnective [Nothing, Just (Command "land"), Nothing] [f1, f2] = Connected Conjunction f1 f2
makeConnective [Nothing, Just (Command "lor"), Nothing] [f1, f2] = Connected Disjunction f1 f2
makeConnective [Nothing, Just (Command "iff"), Nothing] [f1, f2] = Connected Equivalence f1 f2
makeConnective [Just(Command "lnot"), Nothing] [f1] = FormulaNeg f1
makeConnective pat _ = error ("makeConnective does not handle the following connective correctly: " <> show pat)



type StructPhrase = SgPl LexicalPhrase

-- | For example 'an integer' would be
-- > Noun (unsafeReadPhrase "integer[/s]") []
type Noun = NounOf Term
data NounOf a
    = Noun (SgPl LexicalPhrase) [a]
    deriving (Show, Eq, Ord)




type NounPhrase t = NounPhraseOf t Term
-- NOTE: 'NounPhraseOf' is only used with arguments of type 'Term',
-- but keeping the argument parameter @a@ allows the 'Show' and 'Eq'
-- instances to remain decidable.
data NounPhraseOf t a
    = NounPhrase [AdjLOf a] (NounOf a) (t VarSymbol) [AdjROf a] (Maybe Stmt)

instance (Show a, Show (t VarSymbol)) => Show (NounPhraseOf t a) where
    show (NounPhrase ls n vs rs ms) =
        "NounPhrase ("
            <> show ls <> ") ("
            <> show n <> ") ("
            <> show vs <> ") ("
            <> show rs <> ") ("
            <> show ms <> ")"

instance (Eq a, Eq (t VarSymbol)) => Eq (NounPhraseOf t a) where
    NounPhrase ls n vs rs ms == NounPhrase ls' n' vs' rs' ms' =
        ls == ls' && n == n' && vs == vs' && rs == rs' && ms == ms'

-- This is arbitrary and ugly, but it's useful to have a somewhat
-- usable Ord instance for all raw syntax (e.g. for 'nubOrd').
instance (Ord a, Ord (t VarSymbol)) => Ord (NounPhraseOf t a) where
    NounPhrase ls n vs rs ms `compare` NounPhrase ls' n' vs' rs' ms' =
        case compare n n' of
            GT -> case compare ls ls' of
                GT -> case compare rs rs' of
                    GT -> case compare ms ms' of
                        GT -> compare vs vs'
                        ordering -> ordering
                    ordering -> ordering
                ordering -> ordering
            ordering -> ordering

-- | @Nameless a@ is quivalent to @Const () a@ (from "Data.Functor.Const").
-- It describes a container that is unwilling to actually contain something.
-- @Nameless@ lets us treat nouns with no names, one name, or many names uniformly.
-- Thus @NounPhraseOf Nameless a@ is a noun phrase without a name and with arguments
-- of type @a@.
data Nameless a = Nameless deriving (Show, Eq, Ord)


-- | Left adjectives modify nouns from the left side,
-- e.g. /@even@/, /@continuous@/, and /@σ-finite@/.
type AdjL = AdjLOf Term
data AdjLOf a
    = AdjL LexicalPhrase [a]
    deriving (Show, Eq, Ord)


-- | Right attributes consist of basic right adjectives, e.g.
-- /@divisible by ?@/, or /@of finite type@/ and verb phrases
-- marked with /@that@/, such as /@integer that divides n@/.
-- In some cases these right attributes may be followed
-- by an additional such-that phrase.
type AdjR = AdjROf Term
data AdjROf a
    = AdjR LexicalPhrase [a]
    | AttrRThat VerbPhrase
    deriving (Show, Eq, Ord)


-- | Adjectives for parts of the AST where adjectives are not used
-- to modify nouns and the L/R distinction does not matter, such as
-- when then are used together with a copula (like /@n is even@/).
type Adj = AdjOf Term
data AdjOf a
    = Adj LexicalPhrase [a]
    deriving (Show, Eq, Ord)


type Verb = VerbOf Term
data VerbOf a
    = Verb (SgPl LexicalPhrase) [a]
    deriving (Show, Eq, Ord)


type Fun = FunOf Term
data FunOf a
    = Fun (SgPl LexicalPhrase) [a]
    deriving (Show, Eq, Ord)


type VerbPhrase = VerbPhraseOf Term
data VerbPhraseOf a
    = VPVerb (VerbOf a)
    | VPAdj (NonEmpty (AdjOf a)) -- ^ @x is foo@ / @x is foo and bar@
    | VPVerbNot (VerbOf a)
    | VPAdjNot (NonEmpty (AdjOf a)) -- ^ @x is not foo@ / @x is neither foo nor bar@
    deriving (Show, Eq, Ord)


data Quantifier
    = Universally
    | Existentially
    | Nonexistentially
    deriving (Show, Eq, Ord)

data QuantPhrase = QuantPhrase Quantifier (NounPhrase []) deriving (Show, Eq, Ord)


data Term
    = TermExpr Expr
    -- ^ A symbolic expression.
    | TermFun Fun
    -- ^ Definite noun phrase, e.g. /@the derivative of $f$@/.
    | TermIota VarSymbol Stmt
    -- ^ Definite descriptor, e.g. /@an $x$ such that ...@//
    | TermQuantified Quantifier (NounPhrase Maybe)
    -- ^ Indefinite quantified notion, e.g. /@every even integer that divides $k$ ...@/.
    deriving (Show, Eq, Ord)


data Stmt
    = StmtFormula Formula -- ^ E.g.: /@We have \<Formula\>@/.
    | StmtVerbPhrase (NonEmpty Term) VerbPhrase -- ^ E.g.: /@\<Term\> and \<Term\> \<verb\>@/.
    | StmtNoun (NonEmpty Term) (NounPhrase Maybe) -- ^ E.g.: /@\<Term\> is a(n) \<NP\>@/.
    | StmtStruct Term StructPhrase
    | StmtNeg Stmt -- ^ E.g.: /@It is not the case that \<Stmt\>@/.
    | StmtExists (NounPhrase []) -- ^ E.g.: /@There exists a(n) \<NP\>@/.
    | StmtConnected Connective Stmt Stmt
    | StmtQuantPhrase QuantPhrase Stmt
    | SymbolicQuantified Quantifier (NonEmpty VarSymbol) Bound (Maybe Stmt) Stmt
    deriving (Show, Eq, Ord)

data Bound = Unbounded | Bounded Sign Relation Expr deriving (Show, Eq, Ord)

pattern SymbolicForall :: NonEmpty VarSymbol -> Bound -> Maybe Stmt -> Stmt -> Stmt
pattern SymbolicForall vs bound suchThat have = SymbolicQuantified Universally vs bound suchThat have

pattern SymbolicExists :: NonEmpty VarSymbol -> Bound -> Stmt -> Stmt
pattern SymbolicExists vs bound suchThat = SymbolicQuantified Existentially vs bound Nothing suchThat

pattern SymbolicNotExists :: NonEmpty VarSymbol -> Bound -> Stmt -> Stmt
pattern SymbolicNotExists vs bound suchThat = StmtNeg (SymbolicExists vs bound suchThat)

data Asm
    = AsmSuppose Stmt
    | AsmLetNoun (NonEmpty VarSymbol) (NounPhrase Maybe) -- ^ E.g.: /@let k be an integer@/
    | AsmLetIn (NonEmpty VarSymbol) Expr -- ^ E.g.: /@let $k\in\integers$@/
    | AsmLetThe VarSymbol Fun -- ^ E.g.: /@let $g$ be the derivative of $f$@/
    | AsmLetEq VarSymbol Expr -- ^ E.g.: /@let $m = n + k$@/
    | AsmLetStruct VarSymbol StructPhrase -- ^ E.g.: /@let $A$ be a monoid@/
    deriving (Show, Eq, Ord)

data Axiom = Axiom [Asm] Stmt
    deriving (Show, Eq, Ord)

data Lemma = Lemma [Asm] Stmt
    deriving (Show, Eq, Ord)

-- | The head of the definition describes the part before the /@iff@/,
-- i.e. the definiendum. An optional noun-phrase corresponds to an optional
-- type annotation for the 'Term' of the head. The last part of the head
-- is the lexical phrase that is defined.
--
-- > "A natural number   $n$        divides $m$   iff   ..."
-- >  ^^^^^^^^^^^^^^^^   ^^^        ^^^^^^^^^^^         ^^^
-- >  type annotation    variable   verb                definiens
-- >  (a noun phrase)               (all args are vars) (a statement)
--
data DefnHead
    = DefnAdj (Maybe (NounPhrase Maybe)) VarSymbol (AdjOf VarSymbol)
    | DefnVerb (Maybe (NounPhrase Maybe)) VarSymbol (VerbOf VarSymbol)
    | DefnNoun VarSymbol (NounOf VarSymbol)
    | DefnSymbolicPredicate PrefixPredicate (NonEmpty VarSymbol)
    | DefnRel VarSymbol RelationSymbol VarSymbol
    -- ^ E.g.: /@$x \subseteq y$ iff [...@/
    deriving (Show, Eq, Ord)

data Defn
    = Defn [Asm] DefnHead Stmt
    | DefnFun [Asm] (FunOf VarSymbol) (Maybe Term) Term
    -- ^ A 'DefnFun' consists of the functional noun (which must start with /@the@/)
    -- and an optional specification of a symbolic equivalent. The symbolic equivalent
    -- does not need to have the same variables as the full functional noun pattern.
    --
    -- > "The tensor product of $U$ and $V$ over $K$, $U\tensor V$, is ..."
    -- >  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^     ^^^
    -- >  definiendum                                 symbolic eqv.    definiens
    -- >  (a functional noun)                         (an exression)   (a term)
    --
    | DefnOp SymbolPattern Expr
    deriving (Show, Eq, Ord)

data Proof
    = Omitted
    | Qed Justification
    -- ^ Ends of a proof, leaving automation to discharge the current goal using the given justification.
    | ByCase [Case]
    | ByContradiction Proof
    | BySetInduction (Maybe Term) Proof
    -- ^ ∈-induction.
    | ByOrdInduction Proof
    -- ^ Transfinite induction for ordinals.
    | Assume Stmt Proof
    | FixSymbolic (NonEmpty VarSymbol) Bound Proof
    | FixSuchThat (NonEmpty VarSymbol) Stmt Proof
    | Calc Calc Proof
    -- ^ Simplify goals that are implications or disjunctions.
    | TakeVar (NonEmpty VarSymbol) Bound Stmt Justification Proof
    | TakeNoun (NounPhrase []) Justification Proof
    | Have (Maybe Stmt) Stmt Justification Proof
    -- ^ /@Since \<stmt\>, we have \<stmt\> by \<ref\>.@/
    | Suffices Stmt Justification Proof
    -- ^ /@It suffices to show that [...]. [...]@/
    | Subclaim Stmt Proof Proof
    -- ^ A claim is a sublemma with its own proof:
    --  /@Show \<goal stmt\>. \<steps\>. \<continue other proof\>.@/
    | Define VarSymbol Expr Proof
    -- ^ Local definition.
    --
    | DefineFunction VarSymbol VarSymbol Expr VarSymbol Expr Proof
    -- ^ Local function definition, e.g. /@Let $f(x) = e$ for $x\\in d$@/.
    -- The first 'VarSymbol' is the newly defined symbol, the second one is the argument.
    -- The first 'Expr' is the value, the final variable and expr specify a bound (the domain of the function).
    
    
    
    
    | DefineFunctionMathy VarSymbol VarSymbol VarSymbol [VarSymbol Expr [VarSymbol] Expr ] Proof
    -- ^ Local function definition, but in this case we give the domain and target an the rules for $xs$ in some sub domains.
    -- 
    deriving (Show, Eq, Ord)

-- | An inline justification.
data Justification
    = JustificationRef (NonEmpty Marker)
    | JustificationSetExt
    | JustificationEmpty
    | JustificationLocal -- ^ Use only local assumptions
    deriving (Show, Eq, Ord)


-- | A case of a case split.
data Case = Case
    { caseOf :: Stmt
    , caseProof :: Proof
    } deriving (Show, Eq, Ord)

data Calc
    = Equation Expr (NonEmpty (Expr, Justification))
    -- ^ A chain of equalities. Each claimed equality has a (potentially empty) justification.
    -- For example: @a &= b \\explanation{by \\cref{a_eq_b}} &= c@
    -- would be (modulo expr constructors)
    -- @Equation "a" [("b", JustificationRef "a_eq_b"), ("c", JustificationEmpty)]@.
    | Biconditionals Formula (NonEmpty (Formula, Justification))
    deriving (Show, Eq, Ord)


data Abbreviation
    = AbbreviationAdj VarSymbol (AdjOf VarSymbol) Stmt
    | AbbreviationVerb VarSymbol (VerbOf VarSymbol) Stmt
    | AbbreviationNoun VarSymbol (NounOf VarSymbol) Stmt
    | AbbreviationRel VarSymbol RelationSymbol VarSymbol Stmt
    | AbbreviationFun (FunOf VarSymbol) Term
    | AbbreviationEq SymbolPattern Expr
    deriving (Show, Eq, Ord)

data Datatype
    = DatatypeFin (NounOf Term) (NonEmpty Text)
    deriving (Show, Eq, Ord)

data Inductive = Inductive
    { inductiveSymbolPattern :: SymbolPattern
    , inductiveDomain :: Expr
    , inductiveIntros :: NonEmpty IntroRule
    }
    deriving (Show, Eq, Ord)

data IntroRule = IntroRule
    { introConditions :: [Formula] -- The inductively defined set may only appear as an argument of monotone operations on the rhs.
    , introResult :: Formula -- TODO Refine.
    }
    deriving (Show, Eq, Ord)


data SymbolPattern = SymbolPattern FunctionSymbol [VarSymbol]
    deriving (Show, Eq, Ord)

data Signature
    = SignatureAdj  VarSymbol (AdjOf  VarSymbol)
    | SignatureVerb VarSymbol (VerbOf VarSymbol)
    | SignatureNoun VarSymbol (NounOf VarSymbol)
    | SignatureSymbolic SymbolPattern (NounPhrase Maybe)
    -- ^ /@$\<symbol\>(\<vars\>)$ is a \<noun\>@/
    deriving (Show, Eq, Ord)


data StructDefn = StructDefn
    { structPhrase :: StructPhrase
    -- ^ E.g.: @partial order@ or @abelian group@.\
    , structParents :: [StructPhrase]
    -- ^ Structural parents
    , structLabel :: VarSymbol
    , structFixes :: [StructSymbol]
    -- ^ List of text for commands representing constants not inherited from its parents,
    -- e.g.: @\sqsubseteq@ or @\inv@.
    , structAssumes :: [(Marker, Stmt)]
    }
    deriving (Show, Eq, Ord)

newtype Marker = Marker Text deriving (Show, Eq, Ord, Generic)

deriving newtype instance Hashable Marker

instance IsString Marker where
    fromString str = Marker (Text.pack str)

data Block
    = BlockAxiom SourcePos Marker Axiom
    | BlockLemma SourcePos Marker Lemma
    | BlockProof SourcePos Proof
    | BlockDefn SourcePos Marker Defn
    | BlockAbbr SourcePos Marker Abbreviation
    | BlockData SourcePos Datatype
    | BlockInductive SourcePos Marker Inductive
    | BlockSig SourcePos [Asm] Signature
    | BlockStruct SourcePos Marker StructDefn
    deriving (Show, Eq, Ord)
