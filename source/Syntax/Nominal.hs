{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

-- | Nominal variant of the internal (semantic) syntax tree.
module Syntax.Nominal
    ( module Syntax.Nominal
    , module Syntax.Abstract
    , module Syntax.LexicalPhrase
    , module Syntax.Token
    ) where


import Base
import Control.Monad (foldM)
import Control.Monad.State.Strict (State, evalState, get, put)
import Syntax.Lexicon (pattern PairSymbol, pattern ConsSymbol)
import Syntax.LexicalPhrase (unsafeReadPhrase, unsafeReadPhraseSgPl)
import Syntax.Token (Token(..))
import Report.Location

import Syntax.Abstract
    ( Chain(..)
    , Associativity(..)
    , Connective(..)
    , VarSymbol(..)
    , FunctionSymbol
    , MixfixItem(..)
    , Pattern(..)
    , LexicalItem
    , LexicalItemSgPl
    , RelationSymbol(..)
    , StructSymbol (..)
    , Relation
    , VarSymbol(..)
    , PropositionalConstant(..)
    , StructPhrase
    , Justification(..)
    , Marker(..)
    , markerFromToken
    , lexicalItemMarker
    , lexicalItemSgPlMarker
    , mkLexicalItem
    , mkLexicalItemSgPl
    , relationSymbolMarker
    , relationSymbolToken
    , mixfixMarker
    , mkMixfixItem
    , pattern CarrierSymbol, pattern ConsSymbol, pattern ElementSymbol
    , pattern NotElementSymbol, pattern EqSymbol, pattern NeqSymbol, pattern SubseteqSymbol
    )

import Data.HashMap.Strict qualified as HM
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import TextBuilder (TextBuilder)

-- | 'Symbol's can be used as function and relation symbols.
data Symbol
    = SymbolMixfix FunctionSymbol
    | SymbolFun LexicalItemSgPl
    | SymbolInteger Int
    | SymbolPredicate Predicate
    deriving (Show, Eq, Ord, Generic, Hashable)


data Predicate
    = PredicateAdj LexicalItem
    | PredicateVerb LexicalItemSgPl
    | PredicateNoun LexicalItemSgPl -- ^ /@<...> is a <...>@/.
    | PredicateRelation RelationSymbol
    | PredicateSymbol Text
    | PredicateNounStruct LexicalItemSgPl -- ^ /@<...> is a <...>@/.
    deriving (Show, Eq, Ord, Generic, Hashable)


data Quantifier
    = Universally
    | Existentially
    deriving (Show, Eq, Ord, Generic, Hashable)

type Formula = Term
type Term = Expr
data Name = Name
    { occ :: VarSymbol
    , uniq :: Int
    }
    deriving (Show, Eq, Ord, Generic, Hashable)

instance IsString Name where
    fromString str = Name (fromString str) 0

nameOf :: VarSymbol -> Name
nameOf v = Name v 0

freshName :: Int -> Name
freshName n = Name (FreshVar n) n


-- | Internal higher-order expressions with explicit nominal binders.
--
-- In this representation, binders directly store their bound variable names.
-- Capture-avoiding substitution is handled by the Rapier algorithm implemented
-- below ('rapierSubstitute').
data Expr
    = TermVar Name
    -- ^ Fresh constants disjoint from all user-named identifiers.
    -- These can be used to eliminate higher-order constructs.
    --
    | TermSymbol Location Symbol [Expr]
    -- ^ Application of a symbol (including function and predicate symbols).
    | TermSymbolStruct StructSymbol (Maybe Expr)
    --
    | Apply Expr (NonEmpty Expr)
    -- ^ Higher-order application.
    --
    | TermSep Name Expr Expr
    -- ^ Set comprehension using seperation, e.g.: /@{ x ∈ X | P(x) }@/.
    -- The bound variable scopes over the final expression only.
    --
    | ReplacePred Name Name Expr Expr
    -- ^ Replacement for single-valued predicates. The concrete syntax for these
    -- syntactically requires a bounded existential quantifier in the condition:
    --
    -- /@$\{ y | \exists x\in A. P(x,y) \}$@/
    --
    -- In definitions the single-valuedness of @P@ becomes a proof obligation.
    --
    -- The first variable is the range variable (typically @y@),
    -- the second variable is the domain variable (typically @x@).
    -- Both scope over the final expression.
    --
    | ReplaceFun (NonEmpty (Name, Expr)) Expr Expr
    -- ^ Set comprehension using functional replacement,
    -- e.g.: /@{ f(x, y) | x ∈ X; y ∈ Y; P(x, y) }@/.
    --
    -- Bound variables scope sequentially over later domains, and over the
    -- final two expressions.
    --
    | Connected Connective Expr Expr
    | Lambda [Name] Expr
    | Quantified Quantifier [Name] Expr
    | PropositionalConstant PropositionalConstant
    | Not Location Expr
    deriving (Show, Eq, Ord, Generic, Hashable)


abstractVarSymbol :: Name -> Expr -> ([Name], Expr)
abstractVarSymbol x e = ([x], e)

abstractVarSymbols :: Foldable t => t Name -> Expr -> ([Name], Expr)
abstractVarSymbols xs e = (toList xs, e)


forgetLocation :: Expr -> Expr
forgetLocation = \case
      TermVar a ->
        TermVar a

      TermSymbol _loc symb args ->
        TermSymbol Nowhere symb (map forgetLocation args)

      TermSymbolStruct ss me ->
        TermSymbolStruct ss (forgetLocation <$> me)

      Apply f args ->
        Apply (forgetLocation f) (forgetLocation <$> args)

      TermSep v dom body ->
        TermSep v (forgetLocation dom) (forgetLocation body)

      ReplacePred v1 v2 dom body ->
        ReplacePred v1 v2 (forgetLocation dom) (forgetLocation body)

      ReplaceFun doms lhs rhs ->
        ReplaceFun
          (fmap (fmap forgetLocation) doms)
          (forgetLocation lhs)
          (forgetLocation rhs)

      Connected c e1 e2 ->
        Connected c (forgetLocation e1) (forgetLocation e2)

      Lambda bs body ->
        Lambda bs (forgetLocation body)

      Quantified q bs body ->
        Quantified q bs (forgetLocation body)

      PropositionalConstant pc ->
        PropositionalConstant pc

      Not _loc e ->
        Not Nowhere (forgetLocation e)


equivalent :: Expr -> Expr -> Bool
equivalent e1 e2 = forgetLocation e1 == forgetLocation e2


shadowVars :: Foldable t => t Name -> Set Name -> HashMap StructSymbol Name -> (Set Name, HashMap StructSymbol Name)
shadowVars vars labels ops = foldl' step (labels, ops) vars
  where
    step (labels', ops') v = (Set.delete v labels', HM.filter (/= v) ops')

-- | Use the given set of in scope structures to cast them to their carriers
-- when occurring on the rhs of the element relation.
-- Use the given 'Map' to annotate (unannotated) structure operations
-- with the most recent inscope appropriate label.
annotateWith :: Set Name -> HashMap StructSymbol Name -> Formula -> Formula
annotateWith = go
    where
        go :: Set Name -> HashMap StructSymbol Name -> Expr -> Expr
        go labels ops = \case
            TermSymbolStruct symb Nothing ->
                -- TODO error if symbol is not instantiated, but only in theorems?
                TermSymbolStruct symb (TermVar <$> HM.lookup symb ops)
            e@TermSymbolStruct{} ->
                e
            IsElementOf loc1 a (TermVar x) | x `Set.member` labels ->
                IsElementOf loc1 (go labels ops a) (TermSymbolStruct CarrierSymbol (Just (TermVar x)))
            Not loc a ->
                Not loc (go labels ops a)
            Connected conn a b ->
                Connected conn (go labels ops a) (go labels ops b)
            Quantified quant bs body ->
                let (labels', ops') = shadowVars bs labels ops
                in Quantified quant bs (go labels' ops' body)
            Lambda bs body ->
                let (labels', ops') = shadowVars bs labels ops
                in Lambda bs (go labels' ops' body)
            e@TermVar{} -> e
            TermSymbol loc symb args ->
                TermSymbol loc symb (go labels ops <$> args)
            Apply e1 args ->
                Apply (go labels ops e1) (go labels ops <$> args)
            TermSep vs e body ->
                let (labels', ops') = shadowVars [vs] labels ops
                in TermSep vs (go labels ops e) (go labels' ops' body)
            ReplacePred y x xB body ->
                let (labels', ops') = shadowVars [x, y] labels ops
                in ReplacePred y x (go labels ops xB) (go labels' ops' body)
            ReplaceFun bounds ap cond ->
                let (bounds', labels', ops') = annotateBounds labels ops (toList bounds)
                in ReplaceFun
                    (NonEmpty.fromList bounds')
                    (go labels' ops' ap)
                    (go labels' ops' cond)
            e@PropositionalConstant{} -> e

        annotateBounds
            :: Set Name
            -> HashMap StructSymbol Name
            -> [(Name, Expr)]
            -> ([(Name, Expr)], Set Name, HashMap StructSymbol Name)
        annotateBounds labels ops = \case
            [] -> ([], labels, ops)
            (x, dom) : rest ->
                let dom' = go labels ops dom
                    (labels', ops') = shadowVars [x] labels ops
                    (rest', labels'', ops'') = annotateBounds labels' ops' rest
                in ((x, dom') : rest', labels'', ops'')

containsHigherOrderConstructs :: Expr -> Bool
containsHigherOrderConstructs = \case
    TermSep {} -> True
    ReplacePred{}-> True
    ReplaceFun{}-> True
    Lambda{} -> True
    Apply{} -> False -- FIXME: this is a lie in general; we need to add sortchecking to determine this.
    TermVar{} -> False
    PropositionalConstant{} -> False
    TermSymbol _loc _s es -> any containsHigherOrderConstructs es
    Not _loc e -> containsHigherOrderConstructs e
    Connected _ e1 e2 -> containsHigherOrderConstructs e1 || containsHigherOrderConstructs e2
    Quantified _ _ body -> containsHigherOrderConstructs body
    TermSymbolStruct _ _ -> False

pattern TermOp :: Location -> FunctionSymbol -> [Expr] -> Expr
pattern TermOp loc op es = TermSymbol loc (SymbolMixfix op) es

pattern TermConst :: Location -> Token -> Expr
pattern TermConst loc c <- TermOp loc (MixfixItem (TokenCons c End) _ NonAssoc) []
    where
        TermConst loc c =
            TermOp loc (MixfixItem (TokenCons c End) (markerFromToken c) NonAssoc) []

pattern TermPair :: Location -> Expr -> Expr -> Expr
pattern TermPair loc e1 e2 = TermOp loc PairSymbol [e1, e2]

pattern Atomic :: Location -> Predicate -> [Expr] -> Expr
pattern Atomic loc symbol args = TermSymbol loc (SymbolPredicate symbol) args


pattern FormulaAdj :: Location -> Expr -> LexicalItem -> [Expr] -> Expr
pattern FormulaAdj loc e adj es = Atomic loc (PredicateAdj adj) (e:es)

pattern FormulaVerb :: Location -> Expr -> LexicalItemSgPl -> [Expr] -> Expr
pattern FormulaVerb loc e verb es = Atomic loc (PredicateVerb verb) (e:es)

pattern FormulaNoun :: Location -> Expr -> LexicalItemSgPl -> [Expr] -> Expr
pattern FormulaNoun loc e noun es = Atomic loc (PredicateNoun noun) (e:es)

relationNoun :: Location -> Expr -> Formula
relationNoun loc arg = FormulaNoun loc arg (mkLexicalItemSgPl (unsafeReadPhraseSgPl "relation[/s]") "relation") []

rightUniqueAdj :: Location -> Expr -> Formula
rightUniqueAdj loc arg = FormulaAdj loc arg (mkLexicalItem (unsafeReadPhrase "right-unique") "rightunique") []

-- | Untyped quantification.
pattern Forall, Exists :: Name -> Expr -> Expr
pattern Forall x body = Quantified Universally [x] body
pattern Exists x body = Quantified Existentially [x] body

makeForall, makeExists :: Foldable t => t VarSymbol -> Formula -> Formula
makeForall xs e = foldr (\x acc -> Forall (nameOf x) acc) e (toList xs)
makeExists xs e = foldr (\x acc -> Exists (nameOf x) acc) e (toList xs)

instantiateSome :: NonEmpty VarSymbol -> [VarSymbol] -> [VarSymbol]
instantiateSome xs = List.filter (`notElem` toList xs)

isClosed :: Expr -> Bool
isClosed = Set.null . freeVars

-- | Bind all free variables not occuring in the given set universally.
-- The exclusion set is matched against the occurrence name ('occ').
forallClosure :: Set VarSymbol -> Formula -> Formula
forallClosure xs phi = if isClosed phi
    then phi
    else if null toBind
        then phi
        else Quantified Universally toBind phi
  where
    toBind = [x | x <- Set.toList (freeVars phi), occ x `Set.notMember` xs]


freeVars :: Expr -> Set Name
freeVars = \case
    TermVar x -> Set.singleton x
    TermSymbol _ _ args -> foldl' (<>) Set.empty (freeVars <$> args)
    TermSymbolStruct _ mArg -> maybe Set.empty freeVars mArg
    Apply f args -> freeVars f <> foldl' (<>) Set.empty (freeVars <$> toList args)
    TermSep x dom body -> freeVars dom <> (freeVars body Set.\\ Set.singleton x)
    ReplacePred y x dom body -> freeVars dom <> (freeVars body Set.\\ Set.fromList [x, y])
    ReplaceFun bounds lhs rhs ->
        let (bound, domFree) = foldl' step (Set.empty, Set.empty) (toList bounds)
            lhsFree = freeVars lhs Set.\\ bound
            rhsFree = freeVars rhs Set.\\ bound
        in domFree <> lhsFree <> rhsFree
      where
        step (bound, acc) (x, dom) =
            let domFree = freeVars dom Set.\\ bound
            in (Set.insert x bound, acc <> domFree)
    Connected _ e1 e2 -> freeVars e1 <> freeVars e2
    Lambda bs body -> freeVars body Set.\\ Set.fromList bs
    Quantified _ bs body -> freeVars body Set.\\ Set.fromList bs
    PropositionalConstant _ -> Set.empty
    Not _ e -> freeVars e


-- | Rapier substitution environment.
--
-- * @rapierSubst@ maps in-variables to out-expressions.
-- * @rapierInScope@ is the no-shadowing in-scope set.
-- * @rapierFreshStart@ seeds fresh-name generation.
data RapierEnv = RapierEnv
    { rapierSubst :: HashMap Name Expr
    , rapierInScope :: Set Name
    , rapierFreshStart :: Int
    }
    deriving (Show, Eq, Ord)

mkRapierEnv :: HashMap Name Expr -> Expr -> RapierEnv
mkRapierEnv subst expr = RapierEnv
    { rapierSubst = subst
    , rapierInScope = freeVars expr <> foldMap freeVars (HM.elems subst)
    , rapierFreshStart = 1 + maxUnique (freeVars expr <> foldMap freeVars (HM.elems subst))
    }

maxUnique :: Set Name -> Int
maxUnique = foldl' (\n x -> max n (uniq x)) (-1)

freshNotIn :: Set Name -> State Int Name
freshNotIn inscope = do
    n <- get
    let candidate = freshName n
    put (n + 1)
    if candidate `Set.member` inscope
        then freshNotIn inscope
        else return candidate

data RapierContext = RapierContext
    { ctxSubst :: HashMap Name Expr
    , ctxInScope :: Set Name
    }

rapierSubstituteWithEnv :: RapierEnv -> Expr -> Expr
rapierSubstituteWithEnv env expr = evalState (go context expr) (rapierFreshStart env)
  where
    context = RapierContext
        { ctxSubst = rapierSubst env
        , ctxInScope = rapierInScope env
        }

    go :: RapierContext -> Expr -> State Int Expr
    go ctx = \case
        TermVar v ->
            return $ fromMaybe (TermVar v) (HM.lookup v (ctxSubst ctx))

        TermSymbol loc symb args ->
            TermSymbol loc symb <$> traverse (go ctx) args

        TermSymbolStruct ss me ->
            TermSymbolStruct ss <$> traverse (go ctx) me

        Apply f args ->
            Apply <$> go ctx f <*> traverse (go ctx) args

        TermSep x dom body -> do
            dom' <- go ctx dom
            (x', bodyCtx) <- enterBinder x ctx
            body' <- go bodyCtx body
            return (TermSep x' dom' body')

        ReplacePred y x dom body -> do
            dom' <- go ctx dom
            (x', bodyCtx1) <- enterBinder x ctx
            (y', bodyCtx2) <- enterBinder y bodyCtx1
            body' <- go bodyCtx2 body
            return (ReplacePred y' x' dom' body')

        ReplaceFun bounds lhs rhs -> do
            (bounds', bodyCtx) <- renameBounds ctx (toList bounds)
            lhs' <- go bodyCtx lhs
            rhs' <- go bodyCtx rhs
            return (ReplaceFun (NonEmpty.fromList bounds') lhs' rhs')

        Connected conn e1 e2 ->
            Connected conn <$> go ctx e1 <*> go ctx e2

        Lambda binders body -> do
            (binders', bodyCtx) <- enterBinders binders ctx
            body' <- go bodyCtx body
            return (Lambda binders' body')

        Quantified quant binders body -> do
            (binders', bodyCtx) <- enterBinders binders ctx
            body' <- go bodyCtx body
            return (Quantified quant binders' body')

        PropositionalConstant pc ->
            return (PropositionalConstant pc)

        Not loc e ->
            Not loc <$> go ctx e

    renameBounds
        :: RapierContext
        -> [(Name, Expr)]
        -> State Int ([(Name, Expr)], RapierContext)
    renameBounds ctx = \case
        [] -> return ([], ctx)
        (x, dom) : rest -> do
            dom' <- go ctx dom
            (x', ctx') <- enterBinder x ctx
            (rest', ctx'') <- renameBounds ctx' rest
            return ((x', dom') : rest', ctx'')

    enterBinders :: [Name] -> RapierContext -> State Int ([Name], RapierContext)
    enterBinders binders ctx = do
        (revBs, bodyCtx) <- foldM step ([], ctx) binders
        return (reverse revBs, bodyCtx)
      where
        step (revBs, c) b = do
            (b', c') <- enterBinder b c
            return (b' : revBs, c')

    enterBinder :: Name -> RapierContext -> State Int (Name, RapierContext)
    enterBinder x ctx
        | x `Set.member` (ctxInScope ctx) = do
            y <- freshNotIn (ctxInScope ctx)
            let subst' = HM.insert x (TermVar y) (ctxSubst ctx)
                inscope' = Set.insert y (ctxInScope ctx)
            return (y, RapierContext subst' inscope')
        | otherwise =
            let subst' = HM.delete x (ctxSubst ctx)
                inscope' = Set.insert x (ctxInScope ctx)
            in return (x, RapierContext subst' inscope')


rapierSubstitute :: HashMap Name Expr -> Expr -> Expr
rapierSubstitute subst expr = rapierSubstituteWithEnv (mkRapierEnv subst expr) expr

substituteVar :: Name -> Expr -> Expr -> Expr
substituteVar x rhs = rapierSubstitute (HM.singleton x rhs)

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


pattern Relation :: Location -> RelationSymbol -> [Expr] -> Expr
pattern Relation loc rel es = Atomic loc (PredicateRelation rel) es

-- | Membership.
pattern IsElementOf :: Location -> Expr -> Expr -> Expr
pattern IsElementOf loc e1 e2 = Relation loc ElementSymbol (e1 : [e2])

isElementOf :: Expr -> Expr -> Expr
isElementOf e1 e2 = Relation Nowhere ElementSymbol (e1 : [e2])

-- | Membership.
isNotElementOf :: Location -> Expr -> Expr -> Expr
isNotElementOf loc e1 e2 = Not loc (IsElementOf loc e1 e2)

-- | Subset relation (non-strict).
pattern IsSubsetOf :: Location -> Expr -> Expr -> Expr
pattern IsSubsetOf loc e1 e2 = Atomic loc (PredicateRelation SubseteqSymbol) (e1 : [e2])

ordinalNoun :: LexicalItemSgPl
ordinalNoun = mkLexicalItemSgPl (unsafeReadPhraseSgPl "ordinal[/s]") "ordinal"

isOrdinalNoun :: LexicalItemSgPl -> Bool
isOrdinalNoun noun = noun == ordinalNoun

-- | Ordinal predicate.
pattern IsOrd :: Location -> Expr -> Expr
pattern IsOrd loc e1 <- Atomic loc (PredicateNoun (isOrdinalNoun -> True)) [e1]
    where
        IsOrd loc e1 = Atomic loc (PredicateNoun ordinalNoun) [e1]

-- | Equality.
pattern Equals :: Location -> Expr -> Expr -> Expr
pattern Equals loc e1 e2 = Atomic loc (PredicateRelation EqSymbol) (e1 : [e2])

equals :: Expr -> Expr -> Expr
equals e1 e2 = Atomic Nowhere (PredicateRelation EqSymbol) (e1 : [e2])

-- | Disequality.
pattern NotEquals :: Location -> Expr -> Expr -> Expr
pattern NotEquals loc e1 e2 = Atomic loc (PredicateRelation NeqSymbol) (e1 : [e2])

pattern EmptySet :: Location -> Expr
pattern EmptySet loc =
    TermSymbol loc
        (SymbolMixfix (MixfixItem (TokenCons (Command "emptyset") End) "emptyset" NonAssoc))
        []

makeConjunction :: [Expr] -> Expr
makeConjunction = \case
    [] -> Top
    es -> List.foldl1' And es

makeDisjunction :: [Expr] -> Expr
makeDisjunction = \case
    [] -> Bottom
    es -> List.foldl1' Or es

makeIff :: [Expr] -> Expr
makeIff = \case
    [] -> Bottom
    es -> List.foldl1' Iff es

makeXor :: [Expr] -> Expr
makeXor = \case
    [] -> Bottom
    es -> List.foldl1' Xor es

finiteSet :: NonEmpty (Expr) -> Expr
finiteSet = foldr cons (EmptySet Nowhere)
    where
        cons x y = TermSymbol Nowhere (SymbolMixfix ConsSymbol) [x, y]

isPositive :: Expr -> Bool
isPositive = \case
    Not _ _ -> False
    _ -> True

dual :: Expr -> Expr
dual = \case
    Not _loc f -> f
    f -> Not Nowhere f



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
    | DefnFun [Asm] LexicalItemSgPl [VarSymbol] Term
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

data CalcQuantifier
    = CalcForall (NonEmpty VarSymbol) (Maybe Formula)
    | CalcUnquantified
    deriving (Show, Eq, Ord)

data Proof
    = Omitted
    -- ^ Ends a proof without further verification.
    -- This results in a “gap” in the formalization.
    | Qed {mloc :: Maybe Location, by :: Justification}
    -- ^ Ends of a proof, leaving automation to discharge the current goal using the given justification.
    | ByContradiction Location Proof
    -- ^ Take the dual of the current goal as an assumption and
    -- set the goal to absurdity.
    | BySetInduction Location (Maybe Term) Proof
    -- ^ ∈-induction.
    | ByOrdInduction Location Proof
    -- ^ Transfinite induction for ordinals.
    | Assume Location Formula Proof
    -- ^ Simplify goals that are implications or disjunctions.
    | Fix Location (NonEmpty VarSymbol) Formula Proof
    -- ^ Simplify universal goals (with an optional bound or such that statement)
    | Take Location (NonEmpty VarSymbol) Formula Justification Proof
    -- ^ Use existential assumptions.
    | Suffices Location Formula Justification Proof
    | ByCase Location [Case]
    -- ^ Proof by case. Disjunction of the case hypotheses 'Case'
    -- must hold for this step to succeed. Each case starts a subproof,
    -- keeping the same goal but adding the case hypothesis as an assumption.
    -- Often this will be a classical split between /@P@/ and /@not P@/, in
    -- which case the proof that /@P or not P@/ holds is easy.
    --
    | Have Location Formula Justification Proof
    -- ^ An affirmation, e.g.: /@We have <stmt> by <ref>@/.
    --
    | Calc Location CalcQuantifier Calc Proof
    | Subclaim Location Formula Proof Proof
    -- ^ A claim is a sublemma with its own proof:
    --
    -- /@Show <goal stmt>. <steps>. <continue other proof>.@/
    --
    -- A successful first proof adds the claimed formula as an assumption
    -- for the remaining proof.
    --
    | Define Location VarSymbol Term Proof
    | DefineFunction Location VarSymbol VarSymbol Term Term Proof

    | DefineFunctionLocal Location VarSymbol VarSymbol VarSymbol Term (NonEmpty (Term, Formula)) Proof

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

calcQuant :: CalcQuantifier -> (Formula -> Formula)
calcQuant = \case
    CalcUnquantified -> id
    CalcForall xs maySuchThat -> case maySuchThat of
        Nothing -> makeForall xs
        Just suchThat -> \phi -> makeForall xs (suchThat `Implies` phi)

calcResult :: CalcQuantifier -> Calc -> Expr
calcResult quant = \case
    Equation e eqns -> calcQuant quant (Equals Nowhere e (fst (NonEmpty.last eqns)))
    Biconditionals phi phis -> calcQuant quant (phi `Iff` fst (NonEmpty.last phis))

calculation :: CalcQuantifier -> Calc -> [(Expr, Justification)]
calculation quant = \case
    Equation e1 eqns@((e2, jst) :| _) -> (calcQuant quant (Equals Nowhere e1 e2), jst) : collectEquations quant (toList eqns)
    Biconditionals p1 ps@((p2, jst) :| _) -> (calcQuant quant (p1 `Iff` p2), jst) : collectBiconditionals quant (toList ps)


collectEquations :: CalcQuantifier -> [(Formula, j)] -> [(Formula, j)]
collectEquations quant = \case
    (e1, _) : eqns'@((e2, jst) : _) -> (calcQuant quant (Equals Nowhere e1 e2), jst) : collectEquations quant eqns'
    _ -> []

collectBiconditionals :: CalcQuantifier -> [(Formula, j)] -> [(Formula, j)]
collectBiconditionals quant = \case
    (p1, _) : ps@((p2, jst) : _) -> (calcQuant quant (p1 `Iff` p2), jst) : collectBiconditionals quant ps
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
    -- e.g.: @\contained@ or @\inv@. These are used as default operation names
    -- in instantiations such as @Let $G$ be a group@.
    -- The commands should be set up to handle an optional struct label
    -- which would typically be rendered as a sub- or superscript, e.g.:
    -- @\contained[A]@ could render as ”⊑ᴬ“.
    --    --
    , structDefnAssumes :: [(Marker, Formula)]
    -- ^ The assumption or axioms of the structure.
    -- To be instantiate with the @structFixes@ of a given structure.
    }

deriving instance Show StructDefn
deriving instance Eq   StructDefn
deriving instance Ord  StructDefn


data Abbreviation
    = Abbreviation Symbol (Expr)
    deriving (Show, Eq, Ord)

data Block
    = BlockAxiom Location Marker Axiom
    | BlockLemma Location Marker Lemma
    | BlockProof Location Location Proof
    | BlockDefn Location Marker Defn
    | BlockAbbr Location Marker Abbreviation
    | BlockStruct Location Marker StructDefn
    | BlockInductive Location Marker Inductive
    | BlockSig Location Marker [Asm] Signature
    deriving (Show, Eq, Ord)


data Task = Task
    { taskDirectness :: Directness
    , taskHypotheses :: [Hypothesis] -- ^ No guarantees on order.
    , taskConjectureLabel :: Marker
    , taskLocation :: Location
    , taskConjecture :: Formula
    } deriving (Show, Eq, Generic, Hashable)

data Hypothesis = Hypothesis
    { hypothesisMarker :: Marker
    , hypothesisFormula :: Formula
    , hypothesisEncoded :: TextBuilder
    , hypothesisLine :: TextBuilder
    }

instance Show Hypothesis where
    show (Hypothesis marker formula _ _) =
        "Hypothesis " <> show marker <> " " <> show formula

instance Eq Hypothesis where
    Hypothesis m f _ _ == Hypothesis m' f' _ _ = (m, f) == (m', f')

instance Ord Hypothesis where
    compare (Hypothesis m f _ _) (Hypothesis m' f' _ _) =
        compare (m, f) (m', f')

instance Hashable Hypothesis where
    hashWithSalt s (Hypothesis m f _ _) = hashWithSalt s (m, f)


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


-- | Full boolean contraction.
contraction :: Expr -> Expr
contraction = \case
    Connected conn f1 f2  -> atomicContraction (Connected conn (contraction f1) (contraction f2))
    Quantified quant bs body -> atomicContraction (Quantified quant bs (contraction body))
    Not loc f -> Not loc (contraction f)
    f -> f


-- | Atomic boolean contraction.
atomicContraction :: Expr -> Expr
atomicContraction = \case
    Top    `Iff` f      -> f
    Bottom `Iff` f      -> Not Nowhere f
    f      `Iff` Top    -> f
    f      `Iff` Bottom -> Not Nowhere f

    Top    `Implies` f      -> f
    Bottom `Implies` _      -> Top
    _      `Implies` Top    -> Top
    f      `Implies` Bottom -> Not Nowhere f

    Top    `And` f      -> f
    Bottom `And` _      -> Bottom
    f      `And` Top    -> f
    _      `And` Bottom -> Bottom

    phi@(Quantified _quant _ body) -> case body of
        Top -> Top
        Bottom -> Bottom
        _ -> phi

    Not _ Top    -> Bottom
    Not _ Bottom -> Top

    f -> f
