{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Test.Unit.Syntax (unitTests) where

import Base
import Syntax.DeBruijn

import Test.Tasty
import Test.Tasty.HUnit
import Data.Set qualified as Set

shouldBe :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
shouldBe = flip (assertEqual "")

unitTests :: TestTree
unitTests = testGroup "Terms with scoped de Bruijn indices"
    [ testCase "shift increments indices for matching name and index >= cutoff" shiftBasic
    , testCase "shift respects cutoff (minIndex)" shiftCutoff
    , testCase "shift does not affect variables with different names" shiftDifferent
    , testCase "substitute simple variable replacement" substSimple
    , testCase "substitute is capture-avoiding when binder matches (no replacement under binder)" substShadow
    , testCase "substitute into lambda with different binder works and replacement gets inserted" substLambda
    , testCase "betaReduce performs beta-reduction (capture-avoiding substitution)" betaReduceSimple
    , testCase "alphaReduce renames binders to fresh name '_'" alphaReduceLambda
    , testCase "shift increments only free occurrences under multiple nested binders" shiftNested
    , testCase "shift distinguishes names deeply inside applications" shiftDeepApply
    , testCase "substitute under deep binder shadowing: no substitution occurs" substDeepShadow
    , testCase "substitute with shifting: replacement must lift correctly across multiple binders" substMultiBinder
    , testCase "betaReduce with nested applications and shadowing" betaReduceNested
    , testCase "alphaReduce deeply nested binders" alphaReduceDeep
    , testCase "freeVars: replacement with no binders" freeVarsReplacementSimple
    , testCase "freeVars: replacement with binders that correctly shadow" freeVarsReplacementShadow
    , testCase "freeVars: domains not under binder scope" freeVarsReplacementDomainScope
    , testCase "shift: shift inside Replacement (value and condition)" shiftReplacementSimple
    , testCase "shift: shift respects binder inside replacement" shiftReplacementBinder
    , testCase "substitute: replacement value and condition" substReplacementSimple
    , testCase "substitute: replacement binder shadows target" substReplacementShadow
    , testCase "substitute: replacement binder forces shifting of replacementExpr" substReplacementShift
    , testCase "betaReduce: Replacement unaffected structurally" betaReduceReplacementTest
    , testCase "alphaReduce: Replacement binders renamed correctly" alphaReduceReplacementTest
    ]

-- | Shift x by 1 on Var "x" 0 -> Var "x" 1
shiftBasic :: Assertion
shiftBasic =
    shift 1 "x" 0 (Var "x" 0) `shouldBe` Var "x" 1

-- | Shift with cutoff: when minIndex > var index, don't shift
shiftCutoff :: Assertion
shiftCutoff = do
    let e = Var "x" 0
        actual = shift 1 "x" 1 e -- minIndex = 1, var index = 0 -> unchanged
        expected = Var "x" 0
    actual `shouldBe` expected

-- | Shift doesn't affect variable of different name
shiftDifferent :: Assertion
shiftDifferent = do
    let e = Var "x" 0
        actual = shift 1 "y" 0 e
        expected = Var "x" 0
    actual `shouldBe` expected

-- | Substitution test: replace Var "x" 0 with Var "z" 0
substSimple :: Assertion
substSimple = do
    let targetName = "x"
        targetIndex = 0
        replacement = Var "z" 0
        subject = Var "x" 0
        actual = substitute targetName targetIndex replacement subject
        expected = Var "z" 0
    actual `shouldBe` expected

-- | Substitution should not substitute under a binder that shadows the target name
-- Lambda "x". Var "x" 0 should remain unchanged when substituting (shadowed)
substShadow :: Assertion
substShadow = do
    let targetName = "x"
        targetIndex = 0
        replacement = Var "z" 0
        subject = Lambda "x" (Var "x" 0) -- Lambda x. x[0]
        actual = substitute targetName targetIndex replacement subject
        expected = Lambda "x" (Var "x" 0) -- unchanged because binder shadows
    actual `shouldBe` expected

-- | Substitution into a lambda with a different binder inserts replacement (with correct shifting)
substLambda :: Assertion
substLambda = do
    -- substitute x[0] := z[0] into (Lambda y. x[0])
    let targetName = "x"
        targetIndex = 0
        replacement = Var "z" 0
        subject = Lambda "y" (Var "x" 0)
        actual = substitute targetName targetIndex replacement subject
        -- Expect Lambda y. z[0]  (replacement unaffected by y because replacement name /= y)
        expected = Lambda "y" (Var "z" 0)
    actual `shouldBe` expected

-- 	| β-reduction test: @(Lambda x. x) y  ==> y@
betaReduceSimple :: Assertion
betaReduceSimple = do
    let f = Lambda "x" (Var "x" 0)     -- \x. x
        a = Var "y" 0               -- y
        actual = betaReduce (Apply f a)
        expected = Var "y" 0
    actual `shouldBe` expected

-- | α-reduction test: binder names should be normalized to "_" by 'alphaReduce'
alphaReduceLambda :: Assertion
alphaReduceLambda = do
    let subject = Lambda "x" (Var "x" 0)
        actual = alphaReduce subject
        expected = Lambda "_" (Var "_" 0)
    actual `shouldBe` expected

-- | Shift: deeply nested binders, only free occurrences shift.
-- Expression: Lambda x. Lambda y. Var x 1
-- Shift x by +1 at cutoff 0.
-- Inside Lambda x: minIndex increments, so:
--   Var x 1 should become Var x 2.
shiftNested :: Assertion
shiftNested = do
    let e =
            Lambda "x" (
              Lambda "y" (
                Var "x" 1   -- free relative to binder y, but matches top-level x
              )
            )
        actual = shift 1 "x" 0 e
        expected =
            Lambda "x" (
              Lambda "y" (
                Var "x" 2
              )
            )
    actual `shouldBe` expected


-- | Shift inside nested Apply nodes with multiple variable names.
-- Only matching name (= "a") should shift.
shiftDeepApply :: Assertion
shiftDeepApply = do
    let e =
            Apply
              (Apply (Var "a" 0) (Lambda "b" (Var "a" 1)))
              (Apply (Var "c" 0) (Var "a" 2))
        actual = shift 1 "a" 1 e
        -- All Var "a" with index >= 1 become +1
        expected =
            Apply
              (Apply (Var "a" 0) (Lambda "b" (Var "a" 2)))
              (Apply (Var "c" 0) (Var "a" 3))
    actual `shouldBe` expected


-- | Deep shadowing: substitution must NOT occur beneath *any* binder that captures.
-- Substitute x[0] := z[0]
-- Expression: Lambda x. Lambda x. Var x 0
-- The inner x shadows the outer, and the target is x[0], so nothing changes.
substDeepShadow :: Assertion
substDeepShadow = do
    let replacement = Var "z" 0
        e =
          Lambda "x" (
            Lambda "x" (
              Var "x" 0
            )
          )
        actual = substitute "x" 0 replacement e
        expected = e
    actual `shouldBe` expected


-- | Substitution across multiple binders: replacement must be shifted repeatedly.
-- Substitute x[0] := y[0] into:
--   Lambda a. Lambda b. Var x 0
--
-- Replacement y[0] must be shifted by 1 when crossing binder b, then by 1 again
-- when crossing binder a. Result: Var "y" 2.
substMultiBinder :: Assertion
substMultiBinder = do
    let replacement = Var "y" 0
        e = Lambda "a" (Lambda "b" (Var "x" 0))
        actual = substitute "x" 0 replacement e
        expected = Lambda "a" (Lambda "b" (Var "y" 0))
    actual `shouldBe` expected


-- | β-reduction with nested lambdas, inner shadowing.
-- Apply (Lambda x. Lambda x. x[0]) (Var y 0)
--
-- Call-by-value here:
-- Step 1: Lambda x. Lambda x. x[0] applied to y:
--   substitute x[0] := y shifted
-- But inner binder x shadows, so body stays Lambda x. x[0].
betaReduceNested :: Assertion
betaReduceNested =
    let f = Lambda "x" (Lambda "x" (Var "x" 0))
        arg = Var "y" 0
        actual = betaReduce (Apply f arg)
        expected = Lambda "x" (Var "x" 0)
    in  actual `shouldBe` expected


-- | α-reduction should rename *all* binders consistently, even when nested.
alphaReduceDeep :: Assertion
alphaReduceDeep =
    let actual = alphaReduce (Lambda "x" (Lambda "y" (Lambda "x" (Var "x" 0))))
        expected = Lambda "_" (Lambda "_" (Lambda "_" (Var "_" 0)))
    in  actual `shouldBe` expected

freeVarsReplacementSimple :: Assertion
freeVarsReplacementSimple = do
    -- { x | φ(x) } : represented as ReplacementBody value cond
    let r = Replacement (ReplacementBody (Var "x" 0) (Var "y" 0))
        actual = freeVars r
        expected = Set.fromList ["x","y"]
    actual @?= expected

freeVarsReplacementShadow :: Assertion
freeVarsReplacementShadow = do
    -- { f(x,y) | x ∈ A, x ∈ B }
    -- inner x binds in rest
    let r = Replacement $
                ReplacementBinding "x" (Var "A" 0) $
                    ReplacementBinding "x" (Var "B" 0) $
                        ReplacementBody (Apply (Var "f" 0) (Var "x" 0)) (Var "y" 0)
    freeVars r `shouldBe` Set.fromList ["A","B","f","y"]

freeVarsReplacementDomainScope :: Assertion
freeVarsReplacementDomainScope = do
    let r = Replacement $ ReplacementBinding "x" (Apply {- x is still free here -} (Var "X" 0) (Var "x" 0)) (ReplacementBody (Var "x" 0) (Var "z" 0))
        actual = freeVars r
        -- free vars: X, x (from domain), z (condition)
        expected = Set.fromList ["X","x","z"]
    actual `shouldBe` expected

shiftReplacementSimple :: Assertion
shiftReplacementSimple = do
    let r = Replacement (ReplacementBody (Var "x" 0) (Var "x" 1))
        actual = shift 1 "x" 0 r
        expected = Replacement (ReplacementBody (Var "x" 1) (Var "x" 2)) -- both are free get changed
    actual `shouldBe` expected

shiftReplacementBinder :: Assertion
shiftReplacementBinder = do
    let r = Replacement $ ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "x" 1))
        actual = shift 1 "x" 0 r
        expected = Replacement (ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "x" 2))) -- x0 is bound and remains unchanged
    actual `shouldBe` expected

substReplacementSimple :: Assertion
substReplacementSimple = do
    let r = Replacement $ ReplacementBody (Var "x" 0) (Var "y" 0)
        actual = substitute "x" 0 (Var "z" 0) r
        expected = Replacement $ ReplacementBody (Var "z" 0) (Var "y" 0)
    actual `shouldBe` expected

substReplacementShadow :: Assertion
substReplacementShadow = do
    let r = Replacement (ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "x" 1)))
        actual = substitute "x" 0 (Var "z" 0) r
        expected = Replacement (ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "z" 0))) -- binder shadows x0, only x1 replaced
    actual `shouldBe` expected

substReplacementShift :: Assertion
substReplacementShift = do
    let r = Replacement $ ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "u" 0))
        actual = substitute "x" 0 (Var "y" 0) r
        expected = r -- unchanged, since x0 is bound
    actual `shouldBe` expected

betaReduceReplacementTest :: Assertion
betaReduceReplacementTest = do
    let r = Replacement $ ReplacementBinding "x" (Lambda "a" (Var "a" 0)) (ReplacementBody (Apply (Lambda "b" (Var "b" 0)) (Var "z" 0)) (Var "c" 0))
        actual = betaReduce r
        expected = Replacement $  ReplacementBinding "x" (Lambda "a" (Var "a" 0)) (ReplacementBody (Var "z" 0) (Var "c" 0))
    actual `shouldBe` expected

alphaReduceReplacementTest :: Assertion
alphaReduceReplacementTest = do
    let r = Replacement $ ReplacementBinding "x" (Var "A" 0) (ReplacementBody (Var "x" 0) (Var "B" 0))
        actual = alphaReduce r
        expected = Replacement $ ReplacementBinding "_" (Var "A" 0) (ReplacementBody (Var "_" 0) (Var "B" 0))
    actual `shouldBe` expected
