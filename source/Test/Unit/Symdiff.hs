module Test.Unit.Symdiff where

import Base
import Bound.Scope
import Bound.Var
import Syntax.Internal
import Filter

import Data.Text qualified as Text

filtersWell :: Bool
filtersWell = badFact `notElem` (snd <$> taskHypotheses (filterTask symdiff))


badFact :: ExprOf a
badFact = Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "FreshReplacementVar")), TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (Quantified Existentially (Scope (Connected Conjunction (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (B (NamedVar "A"))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "b")), TermVar (F (TermVar (B (NamedVar "B"))))])) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (F (TermVar (B (NamedVar "FreshReplacementVar")))), TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))]]))))))


symdiff :: Task
symdiff =
    Task
        { taskDirectness =
            Direct
        , taskConjectureLabel = Marker "symdiff_test"
        , taskHypotheses = zipWith (,) (Marker . Text.pack . show <$> ([1..] :: [Int]))
            [ Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "A"))], TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "A"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []], TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "C"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "C"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "x"))], TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []], TermVar (B (NamedVar "x"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "symdiff"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "x"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "Y")), TermVar (B (NamedVar "Z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "Y")), TermVar (B (NamedVar "Z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))], TermVar (B (NamedVar "Z"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Z"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "Y")), TermVar (B (NamedVar "Z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))], TermVar (B (NamedVar "Z"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Z"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "Y")), TermVar (B (NamedVar "Z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "A"))], TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "A"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []], TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "z"))]], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "z"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "C"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "C"))]]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Command "inters"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermSymbol (SymbolMixfix [Just (Command "Pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "A"))]], TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Command "unions"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermSymbol (SymbolMixfix [Just (Command "Pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "A"))]], TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Command "fst"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))]], TermVar (B (NamedVar "a"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Command "snd"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))]], TermVar (B (NamedVar "b"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Just (Command "Pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "A"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Just (Command "Cons"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "X"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermSymbol (SymbolMixfix [Just (Command "emptyset")]) [], TermSymbol (SymbolMixfix [Just (Command "Pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "A"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "neq"))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))], TermVar (B (NamedVar "a"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "neq"))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))], TermVar (B (NamedVar "b"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "A"))]))
            , Quantified Universally (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermSymbol (SymbolMixfix [Just (Command "emptyset")]) [], TermVar (B (NamedVar "a"))]))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "disjoint"), Just (Word "from"), Nothing])) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "disjoint"), Just (Word "from"), Nothing])) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "A"))])))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))])))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "A"))])))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "B"))]))))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))]]) (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "X"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "Y"))]))))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "neq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (Quantified Existentially (Scope (Connected ExclusiveOr (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "c")), TermVar (F (TermVar (B (NamedVar "A"))))]) (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "c")), TermVar (F (TermVar (B (NamedVar "B"))))]))) (Connected Conjunction (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "c")), TermVar (F (TermVar (B (NamedVar "A"))))])) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "c")), TermVar (F (TermVar (B (NamedVar "B"))))])))))))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "B"))])))
            , Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Z"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "Y")), TermVar (B (NamedVar "Z"))]])))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "A"))]) (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "B"))]))) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]])))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "X"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "Y"))])) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))], TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))]])))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "A"))])) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))])))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "C"))])) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "C"))])))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (PropositionalConstant IsTop) (PropositionalConstant IsTop)) (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (Connected Disjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "A"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "B"))])))))
            , Quantified Universally (Scope (Connected Implication (Connected Conjunction (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "x"))])) (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "y"))]))) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))])))
            , Quantified Universally (Scope (Connected Implication (Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (B (NamedVar "A"))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (B (NamedVar "B"))))])))) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))])))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "disjoint"), Just (Word "from"), Nothing])) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (Quantified Universally (Scope (Not (Quantified Existentially (Scope (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (F (TermVar (B (NamedVar "A"))))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (F (TermVar (B (NamedVar "B"))))))])))))))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "A"))]) (Quantified Universally (Scope (Quantified Existentially (Scope (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (F (TermVar (B (NamedVar "A"))))))])))))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "A"))]) (Not (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "A"))])))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "b"))], TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "aprime")), TermVar (B (NamedVar "bprime"))]]) (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "aprime"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "b")), TermVar (B (NamedVar "bprime"))]))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "b")), TermVar (B (NamedVar "c"))]], TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "aprime")), TermSymbol (SymbolMixfix [Just (Word "pair")]) [TermVar (B (NamedVar "bprime")), TermVar (B (NamedVar "cprime"))]]]) (Connected Conjunction (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "aprime"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "b")), TermVar (B (NamedVar "bprime"))])) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "c")), TermVar (B (NamedVar "cprime"))]))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "B")), TermSymbol (SymbolMixfix [Just (Command "Pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "A"))]]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "B")), TermVar (B (NamedVar "A"))])))
            , badFact
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "A"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "B"))]))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]]) (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "A"))]) (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (B (NamedVar "B"))])))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "x")), TermSymbol (SymbolMixfix [Just (Command "Cons"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "y")), TermVar (B (NamedVar "X"))]]) (Connected Disjunction (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "y"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "X"))]))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "z")), TermSymbol (SymbolMixfix [Just (Command "inters"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "X"))]]) (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "X"))]) (Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "Y")), TermVar (F (TermVar (B (NamedVar "X"))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (F (TermVar (B (NamedVar "z")))), TermVar (B (NamedVar "Y"))])))))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "z")), TermSymbol (SymbolMixfix [Just (Command "unions"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "X"))]]) (Quantified Existentially (Scope (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "Y")), TermVar (F (TermVar (B (NamedVar "X"))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (F (TermVar (B (NamedVar "z")))), TermVar (B (NamedVar "Y"))]))))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "subset"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (Quantified Universally (Scope (Connected Conjunction (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (F (TermVar (B (NamedVar "A")))), TermVar (F (TermVar (B (NamedVar "B"))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "neq"))) [TermVar (F (TermVar (B (NamedVar "A")))), TermVar (F (TermVar (B (NamedVar "B"))))]))))))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Symbol "="))) [TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))], TermVar (B (NamedVar "A"))])))
            , Quantified Universally (Scope (Connected Equivalence (TermSymbol (SymbolPredicate (PredicateRelation (Command "subseteq"))) [TermVar (B (NamedVar "A")), TermVar (B (NamedVar "B"))]) (Quantified Universally (Scope (Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (F (TermVar (B (NamedVar "A"))))))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermVar (F (TermVar (F (TermVar (B (NamedVar "B"))))))]))))))))
            , Quantified Universally (Scope (Connected Equivalence (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermSymbol (SymbolMixfix [Nothing, Just (Command "times"), Nothing]) [TermVar (B (NamedVar "X")), TermVar (B (NamedVar "Y"))]])) (Connected Disjunction (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "X"))])) (Not (TermSymbol (SymbolPredicate (PredicateAdj [Just (Word "inhabited")])) [TermVar (B (NamedVar "Y"))])))))
            , Quantified Universally (Scope (Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (F (TermVar (B (NamedVar "y")))), TermVar (B (NamedVar "X"))]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (F (TermVar (B (NamedVar "y")))), TermSymbol (SymbolMixfix [Just (Command "Cons"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR]) [TermVar (B (NamedVar "x")), TermVar (B (NamedVar "X"))]])))))
            , Quantified Universally (Scope (Not (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (NamedVar "a")), TermSymbol (SymbolMixfix [Just (Command "emptyset")]) []])))
            ]
        , taskConjecture =
            Quantified Universally (Scope (Connected Implication (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (FreshVar 0)), TermSymbol (SymbolMixfix [Nothing, Just (Command "setminus"), Nothing]) [TermSymbol (SymbolMixfix [Nothing, Just (Command "union"), Nothing]) [TermVar (F (TermVar (NamedVar "x"))), TermVar (F (TermVar (NamedVar "y")))], TermSymbol (SymbolMixfix [Nothing, Just (Command "inter"), Nothing]) [TermVar (F (TermVar (NamedVar "y"))), TermVar (F (TermVar (NamedVar "x")))]]]) (TermSymbol (SymbolPredicate (PredicateRelation (Command "in"))) [TermVar (B (FreshVar 0)), TermSymbol (SymbolMixfix [Nothing, Just (Command "symdiff"), Nothing]) [TermVar (F (TermVar (NamedVar "x"))), TermVar (F (TermVar (NamedVar "y")))]])))
        }
