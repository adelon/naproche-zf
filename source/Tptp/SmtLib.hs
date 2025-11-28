{-# LANGUAGE NoImplicitPrelude #-}


module Tptp.SmtLib where
-- ^ Export TPTP problems to SMT-LIB S-expressions

import Tptp.UnsortedFirstOrder qualified as Fof
import TextBuilder
import Prelude hiding (head, tail)
import Data.Text qualified as Text
import Data.List.NonEmpty qualified as NonEmpty

buildList :: [TextBuilder] -> TextBuilder
buildList bs = char '(' <> intercalate (char ' ') bs <> char ')'
{-# INLINE buildList #-}

quotedAtom :: TextBuilder -> TextBuilder
quotedAtom b = char '|' <> b <> char '|'
{-# INLINE quotedAtom #-}

buildAtomicWord :: Fof.AtomicWord -> TextBuilder
buildAtomicWord (Fof.AtomicWord w) = if Fof.isProperAtomicWord w then text w else quotedAtom (text w)

buildVariable :: Fof.Variable -> TextBuilder
buildVariable (Fof.Variable v) = text (Text.replace "'" "_" v)

buildApply :: Fof.AtomicWord -> [Fof.Expr] -> TextBuilder
buildApply f args = buildList (buildAtomicWord f : map buildExpr args)

buildExpr :: Fof.Expr -> TextBuilder
buildExpr = \case
    Fof.Apply f [] -> buildAtomicWord f
    Fof.Apply f args -> buildApply f args
    Fof.Var var -> buildVariable var
    Fof.Top -> text "$true"
    Fof.Bottom -> text "$false"
    Fof.Eq t1 t2 -> buildExpr t1 <> char '=' <> buildExpr t2
    Fof.NotEq t1 t2 -> buildExpr t1 <> text "!=" <> buildExpr t2
    Fof.Not f ->
        text "(not " <> buildExpr f <> char ')'
    Fof.Conn Fof.And f1 f2 ->
        text "(and  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
    Fof.Conn Fof.Or f1 f2 ->
        text "(or  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
    Fof.Conn Fof.Imply f1 f2 ->
        text "(=>  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
    Fof.Conn Fof.Iff f1 f2 ->
        text "(=  " <> buildExpr f1 <> char ' ' <> buildExpr f2 <> char ' '
    Fof.Quantified quant vars f ->
        buildQuantifier quant <> char ' ' <>
        buildList (map buildVariable (NonEmpty.toList vars))
        <> char ' ' <> buildExpr f
    where
        buildQuantifier :: Fof.Quantifier -> TextBuilder
        buildQuantifier Fof.Forall = "(forall "
        buildQuantifier Fof.Exists = "(exists "



buildName :: Fof.Name -> TextBuilder
buildName = \case
        Fof.NameAtomicWord w -> buildAtomicWord w
        Fof.NameInt n -> decimal n

buildAnnotatedFormula :: Fof.AnnotatedFormula -> TextBuilder
buildAnnotatedFormula (Fof.AnnotatedFormula _name _role phi) =
        "(assert " <> buildExpr phi <> char ')'

buildTask :: Fof.Task -> TextBuilder
buildTask (Fof.Task fofs) = intercalate (char '\n') decls <> "\n(check-sat)\n"
    where
        decls = "(set-logic UF)" : map buildAnnotatedFormula fofs
