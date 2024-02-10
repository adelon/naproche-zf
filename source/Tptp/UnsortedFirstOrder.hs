{-# LANGUAGE NoImplicitPrelude #-}

-- | A lenient representation of first-order TPTP syntax that does not guarantee that
-- the expression is actually first-order.
module Tptp.UnsortedFirstOrder where

import Data.Char
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as Text
import Prelude hiding (head, tail)
import Prettyprinter
import Prettyprinter.Render.Text
import Text.Builder


isAsciiAlphaNum :: Char -> Bool
isAsciiAlphaNum c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'

-- | A TPTP atomic word, starting with a lowercase letter or enclosed in single quotes.
newtype AtomicWord = AtomicWord Text deriving (Show, Eq, Ord, IsString)

isProperAtomicWord :: Text -> Bool
isProperAtomicWord w = case Text.uncons w of
    Nothing -> False
    Just (head, tail) -> isAsciiLower head && Text.all isAsciiAlphaNum tail

-- | A TPTP variable, written as a word starting with an uppercase letter.
newtype Variable = Variable Text deriving (Show, Eq, Ord, IsString)

isVariable :: Text -> Bool
isVariable var = case Text.uncons var of
    Nothing -> False -- Variables must be nonempty.
    Just (head, tail) -> isAsciiUpper head && Text.all isAsciiAlphaNum tail


data Expr
    = Apply AtomicWord [Expr]
    | Var Variable
    | Top
    | Bottom
    | Eq Expr Expr
    | NotEq Expr Expr
    | Conn Connective Expr Expr
    | Not Expr
    | Quantified Quantifier (NonEmpty Variable) Expr
    deriving (Show, Eq, Ord)

pattern Const :: AtomicWord -> Expr
pattern Const x = Apply x []

data Quantifier = Forall | Exists deriving (Show, Eq, Ord)

data Connective = And | Or | Imply | Iff deriving (Show, Eq, Ord)

data Role
    = Axiom
    | AxiomUseful -- ^ Annotated axiom for trainig premise selection.
    | AxiomRedundant -- ^ Annotated axiom for trainig premise selection.
    | Hypothesis
    | Conjecture
    | NegatedConjecture
    deriving (Show, Eq, Ord)

data Name = NameAtomicWord AtomicWord | NameInt Int
    deriving (Show, Eq, Ord)


data AnnotatedFormula
    = AnnotatedFormula Name Role Expr
    deriving (Show, Eq, Ord)


newtype Task
    = Task [AnnotatedFormula]
    deriving (Show, Eq, Ord, Semigroup, Monoid)

toTextNewline :: Task -> Text
toTextNewline task = run (buildTask task <> char '\n')

toText :: Task -> Text
toText task = run (buildTask task)

singleQuoted :: Text -> Text
singleQuoted str = Text.snoc (Text.cons '\'' (escape str)) '\''
    where
        -- First escape backslashes, then single quotes.
        escape :: Text -> Text
        escape = Text.replace "'" "\\'" . Text.replace "\\" "\\\\"

buildTuple :: [Builder] -> Builder
buildTuple bs = char '(' <> intercalate (char ',') bs <> char ')'

buildList :: [Builder] -> Builder
buildList bs = char '[' <> intercalate (char ',') bs <> char ']'

renderTask :: Task -> Text
renderTask task = renderStrict (layoutPretty defaultLayoutOptions (prettyTask task))

buildAtomicWord :: AtomicWord -> Builder
buildAtomicWord (AtomicWord w) = text if isProperAtomicWord w then w else singleQuoted w

buildVariable :: Variable -> Builder
buildVariable (Variable v) = text (Text.replace "'" "_" v)


buildApply :: AtomicWord -> [Expr] -> Builder
buildApply f args = buildAtomicWord f <> buildTuple (map buildExpr args)

buildExpr :: Expr -> Builder
buildExpr = \case
    Apply f [] -> buildAtomicWord f
    Apply f args -> buildApply f args
    Var var -> buildVariable var
    Top -> text "$true"
    Bottom -> text "$false"
    Eq t1 t2 -> buildExpr t1 <> char '=' <> buildExpr t2
    NotEq t1 t2 -> buildExpr t1 <> text "!=" <> buildExpr t2
    Not f ->
        char '~' <> buildUnitary f
    Conn And f1 f2 ->
        buildAnd f1 <> char '&' <> buildAnd f2
    Conn Or f1 f2 ->
        buildOr f1 <> char '|' <> buildOr f2
    Conn Imply f1 f2 ->
        buildUnitary f1 <> "=>" <> buildUnitary f2
    Conn Iff f1 f2 ->
        buildUnitary f1 <> "<=>" <> buildUnitary f2
    Quantified quant vars f ->
        buildQuantifier quant <> buildList (map buildVariable (NonEmpty.toList vars)) <> char ':' <> buildUnitary f

isAtom :: Expr -> Bool
isAtom = \case
    Var{} -> True
    Apply{} -> True
    Top -> True
    Bottom -> True
    Eq{} -> True
    NotEq{} -> True
    _ -> False

buildQuantifier :: Quantifier -> Builder
buildQuantifier = \case
        Forall -> text "!"
        Exists -> text "?"

buildUnitary :: Expr -> Builder
buildUnitary = \case
    atom | isAtom atom -> buildExpr atom
    Quantified quant vars f ->
        buildQuantifier quant <> buildList (map buildVariable (NonEmpty.toList vars)) <> char ':'  <> buildUnitary f
    Not phi -> char '~' <> buildUnitary phi
    phi -> char '(' <> buildExpr phi <> char ')'

buildAnd :: Expr -> Builder
buildAnd = \case
    Conn And f1 f2 -> buildAnd f1 <> char '&' <> buildAnd f2
    f -> buildUnitary f

buildOr :: Expr -> Builder
buildOr = \case
    Conn Or f1 f2 -> buildOr f1 <> char '|' <> buildUnitary f2
    f -> buildUnitary f

buildName :: Name -> Builder
buildName = \case
        NameAtomicWord w -> buildAtomicWord w
        NameInt n -> decimal n

buildRole :: Role -> Builder
buildRole = \case
        Axiom -> "axiom"
        AxiomUseful -> "axiom_useful"
        AxiomRedundant -> "axiom_redundant"
        Hypothesis -> "hypothesis"
        Conjecture -> "conjecture"
        NegatedConjecture -> "negated_conjecture"

buildAnnotatedFormula :: AnnotatedFormula -> Builder
buildAnnotatedFormula (AnnotatedFormula name role phi) =
        "fof" <> buildTuple [buildName name, buildRole role, buildExpr phi] <> "."

buildTask :: Task -> Builder
buildTask (Task fofs) = intercalate (char '\n') (map buildAnnotatedFormula fofs)



prettyAtomicWord :: AtomicWord -> Doc ann
prettyAtomicWord (AtomicWord w) =
        if isProperAtomicWord w
            then pretty w
            else pretty (singleQuoted w)

prettyVariable :: Variable -> Doc ann
prettyVariable (Variable v) = pretty v


prettyApply :: AtomicWord -> [Expr] -> Doc ann
prettyApply f args = prettyAtomicWord f <> tupled (map prettyExpr args)

-- | @&@ and @|@ are associative, all other connectives are nonassociative.
-- The prettyprinting of these associative connectives does not preserve
-- the precise parenthesization but instead minimizes parentheses in the output.
prettyExpr :: Expr -> Doc ann
prettyExpr = \case
    Apply f [] -> prettyAtomicWord f
    Apply f args -> prettyApply f args
    Var var -> prettyVariable var
    Top -> "$true"
    Bottom -> "$false"
    Eq t1 t2 -> prettyExpr t1 <+> "=" <+> prettyExpr t2
    NotEq t1 t2 -> prettyExpr t1 <+> "!=" <+> prettyExpr t2
    atom | isAtom atom ->
        prettyExpr atom
    Not f ->
        "~" <+> prettyUnitary f
    Conn And f1 f2 ->
        prettyAnd f1 <+> "&" <+> prettyAnd f2
    Conn Or f1 f2 ->
        prettyOr f1 <+> "|" <+> prettyOr f2
    Conn Imply f1 f2 ->
        prettyUnitary f1 <+> "=>" <+> prettyUnitary f2
    Conn Iff f1 f2 ->
        prettyUnitary f1 <+> "<=>" <+> prettyUnitary f2
    Quantified quant vars f ->
        prettyQuantifier quant <+> list (map prettyVariable (NonEmpty.toList vars)) <> ":" <+> prettyUnitary f

prettyQuantifier :: Quantifier -> Doc ann
prettyQuantifier = \case
        Forall -> "!"
        Exists -> "?"

prettyUnitary :: Expr -> Doc ann
prettyUnitary = \case
    atom | isAtom atom -> prettyExpr atom
    Quantified quant vars f ->
        prettyQuantifier quant <+> list (map prettyVariable (NonEmpty.toList vars)) <> ":" <+> prettyUnitary f
    Not phi -> "~" <+> prettyUnitary phi
    phi -> parens (prettyExpr phi)

prettyAnd :: Expr -> Doc ann
prettyAnd = \case
    Conn And f1 f2 -> prettyAnd f1 <+> "&" <+> prettyAnd f2
    f -> prettyUnitary f

prettyOr :: Expr -> Doc ann
prettyOr = \case
    Conn Or f1 f2 -> prettyOr f1 <+> "|" <+> prettyUnitary f2
    f -> prettyUnitary f

prettyName :: Name -> Doc ann
prettyName = \case
        NameAtomicWord w -> prettyAtomicWord w
        NameInt n -> pretty n

prettyRole :: Role -> Doc ann
prettyRole = \case
        Axiom -> "axiom"
        AxiomUseful -> "axiom_useful"
        AxiomRedundant -> "axiom_redundant"
        Hypothesis -> "hypothesis"
        Conjecture -> "conjecture"
        NegatedConjecture -> "negated_conjecture"

prettyAnnotatedFormula :: AnnotatedFormula -> Doc ann
prettyAnnotatedFormula (AnnotatedFormula name role phi) =
        "fof" <> tupled [prettyName name, prettyRole role, prettyExpr phi] <> "."

prettyTask :: Task -> Doc ann
prettyTask (Task fofs) = vsep (map prettyAnnotatedFormula fofs)
