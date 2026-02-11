{-# LANGUAGE OverloadedStrings #-}

module Test.Unit.Nominal (unitTests) where

import Base
import Data.HashMap.Strict qualified as HM
import Data.Set qualified as Set
import Syntax.Nominal

import Test.Tasty
import Test.Tasty.HUnit

shouldBe :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
shouldBe = flip (assertEqual "")

v :: VarSymbol -> Name
v = nameOf

fv :: Int -> Name
fv n = Name (FreshVar n) n

unitTests :: TestTree
unitTests = testGroup "Nominal Rapier"
    [ testCase "substitution under shadowing deletes mapping" testShadowDelete
    , testCase "substitution avoids capture by renaming binder" testCaptureAvoidance
    , testCase "quantifier binder list is renamed only when needed" testQuantifierRename
    , testCase "replace-fun free vars respect sequential scope" testFreeVarsReplaceFun
    , testCase "replace-fun keeps bound variables protected from substitution" testSubstReplaceFunBound
    ]


testShadowDelete :: Assertion
testShadowDelete = do
    let expr = Lambda [v "x"] (TermVar (v "x"))
        actual = substituteVar (v "x") (TermVar (v "a")) expr
        expected = Lambda [v "x"] (TermVar (v "x"))
    actual `shouldBe` expected


testCaptureAvoidance :: Assertion
testCaptureAvoidance = do
    let expr = Lambda [v "y"] (TermVar (v "x"))
        actual = substituteVar (v "x") (TermVar (v "y")) expr
        expected = Lambda [fv 1] (TermVar (v "y"))
    actual `shouldBe` expected


testQuantifierRename :: Assertion
testQuantifierRename = do
    let expr = Quantified Universally [v "x", v "y"] (And (TermVar (v "x")) (TermVar (v "y")))
        actual = substituteVar (v "y") (TermVar (v "x")) expr
        expected = Quantified Universally [fv 1, v "y"] (And (TermVar (fv 1)) (TermVar (v "y")))
    actual `shouldBe` expected


testFreeVarsReplaceFun :: Assertion
testFreeVarsReplaceFun = do
    let expr =
            ReplaceFun
                ((v "x", TermVar (v "a")) :| [(v "y", TermVar (v "x"))])
                (TermVar (v "y"))
                Top
        expected = Set.singleton (v "a")
    freeVars expr `shouldBe` expected


testSubstReplaceFunBound :: Assertion
testSubstReplaceFunBound = do
    let expr =
            ReplaceFun
                ((v "x", TermVar (v "a")) :| [(v "y", TermVar (v "x"))])
                (TermVar (v "x"))
                Top
        subst = HM.singleton (v "x") (TermVar (v "b"))
        actual = rapierSubstitute subst expr
        expected = expr
    actual `shouldBe` expected
