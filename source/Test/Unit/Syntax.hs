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
unitTests = testGroup "Terms with indexed names"
    [ testCase "shift increments indices for matching name and index >= cutoff" do
        shift 1 "x" 0 (Var "x" 0) `shouldBe` Var "x" 1
    , testCase "shift respects cutoff (minIndex)" do
        -- Shift with cutoff: when minIndex > var index, don't shift
        let e = Var "x" 0
            actual = shift 1 "x" 1 e -- minIndex = 1, var index = 0 -> unchanged
            expected = Var "x" 0
        actual `shouldBe` expected
    , testCase "shift does not affect variables with different names" shiftDifferent
    , testCase "shift commutes for distinct variable names (shift_comm)" shiftCommDistinct
    , testCase "nested shifts on same name satisfy shift_shift law" shiftShiftLawSpecialCase
    , testCase "substitute simple variable replacement" substSimple
    , testCase "substitute decrements higher indices of the same name" substUnshiftHigherIndices
    , testCase "substitute is capture-avoiding when binder matches (no replacement under binder)" substShadow
    , testCase "substitute into lambda with different binder works and replacement gets inserted" substLambda
    , testCase "subst x k (x[k]) (shift x k t) = t (subst_shift_id)" substShiftIdLawSpecialCase
    , testCase "subst x k (shift x k v) (shift x k t) = t (subst_shift)" substShiftLawSpecialCase
    , testCase "subst x k u (shift x k v) = v (subst_shift_cancel)" substShiftCancelLawSpecialCase
    , testCase "shift-substitute distributivity when j < k (shift_subst_distrib)" shiftSubstDistribLtCase
    , testCase "shift-substitute distributivity when j >= k (shift_subst_distrib)" shiftSubstDistribGeCase
    , testCase "shift and substitution commute for distinct names (shift_subst_diff)" shiftSubstDiffLawSpecialCase
    , testCase "substitution composition for same name (subst_subst)" substSubstLawSpecialCase
    , testCase "substitution composition for distinct names (subst_subst_diff)" substSubstDiffLawSpecialCase
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
    , testCase "substitute: replacement also decrements higher indices (built-in unshift)" substReplacementUnshiftHigherIndices
    , testCase "substitute: replacement binder shadows target" substReplacementShadow
    , testCase "substitute: replacement binder forces shifting of replacementExpr" substReplacementShift
    , testCase "substitute: replacement with multiple binders and partial shadowing" substReplacementMultiShadow
    , testCase "substitute: replacement substitutes inside domain expressions" substReplacementDomainSubstitution
    , testCase "substitute: replacement shifts inserted expression correctly when binder name matches" substReplacementShiftBinderNameCollision
    , testCase "substitute: replacement under double shadowing binders" substReplacementDoubleShadow
    , testCase "substitute: replacement avoids capture inside condition via shifting" substReplacementCaptureAvoidance


    , testCase "betaReduce: Replacement unaffected structurally" betaReduceReplacementTest
    , testCase "alphaReduce: Replacement binders renamed correctly" alphaReduceReplacementTest

    -- Additional alphaReduceReplacement tests
    , testCase "alphaReduce: multiple binders no shadowing" $ do
        let bs = [("x", Var "A" 0), ("y", Var "B" 0)]
            r = ReplExpr bs (Apply (Var "x" 0) (Var "y" 0)) (Var "C" 0)
            expected = ReplExpr [(defaultVarSymbol, Var "A" 0), (defaultVarSymbol, Var "B" 0)]
                                (Apply (Var defaultVarSymbol 1) (Var defaultVarSymbol 0))
                                (Var "C" 0)
        alphaReduceReplacement r `shouldBe` expected

    , testCase "alphaReduce: binder shadows free variable in value" $ do
        let bs = [("x", Var "A" 0)]
            r = ReplExpr bs (Apply (Var "x" 0) (Var "x" 1)) (Var "y" 0)
            expected = ReplExpr [(defaultVarSymbol, Var "A" 0)] (Apply (Var defaultVarSymbol 0) (Var "x" 0)) (Var "y" 0) -- free x1 gets shifted down to x0
        alphaReduceReplacement r `shouldBe` expected

    , testCase "alphaReduce: multiple nested shadowing" do
        let bs = [("x", Var "A" 0), ("x", Var "B" 0), ("z", Var "C" 0)]
            r = ReplExpr
                bs
                (Apply (Apply (Var "x" 0) (Var "x" 1)) (Var "z" 0)) -- x0, x1, z0 bound
                (Apply (Var "x" 0) (Var "y" 0)) -- x0 bound, y0 free
            -- the inner most variable, z should become 0, the inner x (formerly x0) becomes 1 , the outer x becomes 2
            expected = ReplExpr
                [(defaultVarSymbol, Var "A" 0), (defaultVarSymbol, Var "B" 0), (defaultVarSymbol, Var "C" 0)]
                (Apply (Apply (Var defaultVarSymbol 1) (Var defaultVarSymbol 2)) (Var defaultVarSymbol 0))
                (Apply (Var defaultVarSymbol 1) (Var "y" 0))
            actual = alphaReduceReplacement r
        actual `shouldBe` expected

    , testCase "alphaReduce: free variables not bound remain unchanged" $ do
        let bs = [("x", Var "A" 0), ("y", Var "B" 0)]
            r = ReplExpr bs (Apply (Var "f" 0) (Var "x" 0)) (Var "y" 0)
            expected = ReplExpr [(defaultVarSymbol, Var "A" 0), (defaultVarSymbol, Var "B" 0)]
                                (Apply (Var "f" 0) (Var defaultVarSymbol 1))
                                (Var defaultVarSymbol 0)
        alphaReduceReplacement r `shouldBe` expected

    , testCase "alphaReduce: domains containing binders" $ do
        let bs = [("x", Apply (Var "x" 0) (Var "y" 0)), ("y", Var "B" 0)] -- x0 and y0 are not actually bound in the first domain!
            r = ReplExpr bs (Var "x" 0) (Var "y" 0)
            expected = ReplExpr
                [(defaultVarSymbol, Apply (Var "x" 0) (Var "y" 0)), (defaultVarSymbol, Var "B" 0)]
                (Var defaultVarSymbol 1)
                (Var defaultVarSymbol 0)
        alphaReduceReplacement r `shouldBe` expected
    ]



-- | Shift doesn't affect variable of different name
shiftDifferent :: Assertion
shiftDifferent = do
    let e = Var "x" 0
        actual = shift 1 "y" 0 e
        expected = Var "x" 0
    actual `shouldBe` expected

shiftCommDistinct :: Assertion
shiftCommDistinct = do
    let term =
            Apply
                (Lambda "y" (Apply (Var "x" 0) (Var "y" 0)))
                (Lambda "x" (Apply (Var "x" 0) (Var "y" 1)))
        lhs = shift 1 "x" 0 (shift 1 "y" 1 term)
        rhs = shift 1 "y" 1 (shift 1 "x" 0 term)
    lhs `shouldBe` rhs

shiftShiftLawSpecialCase :: Assertion
shiftShiftLawSpecialCase = do
    let k = 1
        j = 3
        term = Lambda "x" (Apply (Var "x" 2) (Apply (Var "x" 1) (Var "z" 0)))
        lhs = shift 1 "x" j (shift 1 "x" k term)
        rhs = shift 1 "x" k (shift 1 "x" (j - 1) term)
    lhs `shouldBe` rhs

substUnshiftHigherIndices :: Assertion
substUnshiftHigherIndices = do
    let replacement = Var "z" 0
    substitute "x" 1 replacement (Var "x" 3) `shouldBe` Var "x" 2
    substitute "x" 1 replacement (Var "x" 0) `shouldBe` Var "x" 0

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

substShiftIdLawSpecialCase :: Assertion
substShiftIdLawSpecialCase = do
    let term = Apply (Var "x" 1) (Lambda "x" (Apply (Var "x" 1) (Var "x" 0)))
        lhs = substitute "x" 0 (Var "x" 0) (shift 1 "x" 0 term)
    lhs `shouldBe` term

substShiftLawSpecialCase :: Assertion
substShiftLawSpecialCase = do
    let k = 1
        v = Lambda "x" (Apply (Var "x" 0) (Var "x" 2))
        t = Apply (Var "x" 2) (Lambda "y" (Apply (Var "x" 1) (Var "y" 0)))
        lhs = substitute "x" k (shift 1 "x" k v) (shift 1 "x" k t)
    lhs `shouldBe` t

substShiftCancelLawSpecialCase :: Assertion
substShiftCancelLawSpecialCase = do
    let k = 1
        u = Lambda "x" (Var "x" 0)
        v = Apply (Var "x" 1) (Apply (Var "x" 3) (Var "w" 0))
        lhs = substitute "x" k u (shift 1 "x" k v)
    lhs `shouldBe` v

shiftSubstDistribLtCase :: Assertion
shiftSubstDistribLtCase = do
    let j = 0
        k = 1
        v = Var "u" 0
        t = Apply (Var "x" 0) (Lambda "x" (Apply (Var "x" 1) (Var "x" 0)))
        lhs = shift 1 "x" k (substitute "x" j v t)
        rhs = substitute "x" (if j < k then j else j + 1)
                (shift 1 "x" k v)
                (shift 1 "x" (if j < k then k + 1 else k) t)
    lhs `shouldBe` rhs

shiftSubstDistribGeCase :: Assertion
shiftSubstDistribGeCase = do
    let j = 1
        k = 1
        v = Apply (Var "x" 0) (Var "u" 0)
        t = Apply (Var "x" 2) (Lambda "x" (Apply (Var "x" 2) (Var "x" 1)))
        lhs = shift 1 "x" k (substitute "x" j v t)
        rhs = substitute "x" (if j < k then j else j + 1)
                (shift 1 "x" k v)
                (shift 1 "x" (if j < k then k + 1 else k) t)
    lhs `shouldBe` rhs

shiftSubstDiffLawSpecialCase :: Assertion
shiftSubstDiffLawSpecialCase = do
    let v = Apply (Var "x" 0) (Var "z" 0)
        t = Apply (Var "y" 0) (Lambda "y" (Apply (Var "y" 0) (Var "x" 1)))
        lhs = shift 1 "x" 1 (substitute "y" 0 v t)
        rhs = substitute "y" 0 (shift 1 "x" 1 v) (shift 1 "x" 1 t)
    lhs `shouldBe` rhs

substSubstLawSpecialCase :: Assertion
substSubstLawSpecialCase = do
    let i = 0
        k = 1
        u = Apply (Var "x" 0) (Var "a" 0)
        v = Lambda "x" (Apply (Var "x" 1) (Var "b" 0))
        t = Apply (Var "x" 0) (Apply (Var "x" 2) (Lambda "x" (Var "x" 1)))
        lhs = substitute "x" k v (substitute "x" i u t)
        rhs = substitute "x" i
                (substitute "x" k v u)
                (substitute "x" (k + 1) (shift 1 "x" i v) t)
    lhs `shouldBe` rhs

substSubstDiffLawSpecialCase :: Assertion
substSubstDiffLawSpecialCase = do
    let j = 1
        k = 0
        u = Apply (Var "x" 0) (Var "y" 1)
        v = Lambda "y" (Apply (Var "y" 0) (Var "x" 1))
        t = Apply (Var "y" 2) (Lambda "x" (Apply (Var "x" 0) (Var "y" 1)))
        lhs = substitute "x" k v (substitute "y" j u t)
        rhs = substitute "y" j
                (substitute "x" k v u)
                (substitute "x" k (shift 1 "y" j v) t)
    lhs `shouldBe` rhs

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
-- Replacement y[0] is shifted across binders a and b, but only variables named
-- after those binders are affected. Since replacement variable is y, it remains y[0].
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
--   substitute x[0] := y
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


dummyBinder :: (VarSymbol, Expr)
dummyBinder = ("_", Var "_dummy" 0)


freeVarsReplacementSimple :: Assertion
freeVarsReplacementSimple = do
    let r = ReplExpr [dummyBinder] (Var "x" 0) (Var "y" 0)
        actual   = freeVarsReplacement r
        expected = Set.fromList ["x","y","_dummy"]
    actual @?= expected


freeVarsReplacementShadow :: Assertion
freeVarsReplacementShadow = do
    let bs = [("x", Var "A" 0), ("x", Var "B" 0)]
        r = ReplExpr bs
                     (Apply (Var "f" 0) (Var "x" 0))
                     (Var "y" 0)

        expected = Set.fromList ["A","B","f","y"]
    freeVarsReplacement r `shouldBe` expected


freeVarsReplacementDomainScope :: Assertion
freeVarsReplacementDomainScope = do
    let bs = [("x", Apply (Var "X" 0) (Var "x" 0))]

        r = ReplExpr bs (Var "x" 0) (Var "z" 0)

        expected = Set.fromList ["X","x","z"]
    freeVarsReplacement r `shouldBe` expected



shiftReplacementSimple :: Assertion
shiftReplacementSimple = do
    let r = ReplExpr [dummyBinder] (Var "x" 0) (Var "x" 1)
        actual = shiftReplacement 1 "x" 0 r
        expected = ReplExpr [dummyBinder] (Var "x" 1) (Var "x" 2)
    actual `shouldBe` expected


shiftReplacementBinder :: Assertion
shiftReplacementBinder = do
    let bs = [("x", Var "A" 0)]
        r = ReplExpr bs (Var "x" 0) (Var "x" 1)
        actual = shiftReplacement 1 "x" 0 r
        expected = ReplExpr bs (Var "x" 0) (Var "x" 2)

    actual `shouldBe` expected



substReplacementSimple :: Assertion
substReplacementSimple = do
    let r = ReplExpr [dummyBinder] (Var "x" 0) (Var "y" 0)
        actual   = substituteReplacement "x" 0 (Var "z" 0) r
        expected = ReplExpr [dummyBinder] (Var "z" 0) (Var "y" 0)
    actual `shouldBe` expected

substReplacementUnshiftHigherIndices :: Assertion
substReplacementUnshiftHigherIndices = do
    let bs = [("x", Var "A" 0)]
        r = ReplExpr bs (Var "x" 2) (Var "x" 1)
        actual = substituteReplacement "x" 0 (Var "z" 0) r
        expected = ReplExpr bs (Var "x" 1) (Var "z" 0)
    actual `shouldBe` expected


substReplacementShadow :: Assertion
substReplacementShadow = do
    let bs = [("x", Var "A" 0)]
        r = ReplExpr bs (Var "x" 0) (Var "x" 1)
        actual   = substituteReplacement "x" 0 (Var "z" 0) r
        expected = ReplExpr bs (Var "x" 0) (Var "z" 0)
    actual `shouldBe` expected

substReplacementShift :: Assertion
substReplacementShift = do
    let bs = [("x", Var "A" 0)]
        r = ReplExpr bs (Var "x" 0) (Var "u" 0)
        actual   = substituteReplacement "x" 0 (Var "y" 0) r
        expected = r
    actual `shouldBe` expected

substReplacementMultiShadow :: Assertion
substReplacementMultiShadow = do
    -- Replacement:  for x:A, y:B .  value = x0, cond = y1
    let bs = [("x", Var "A" 0), ("y", Var "B" 0)]
        r  = ReplExpr bs (Var "x" 0) (Var "y" 1)

    -- Substitute x0 := z0
    -- First binder: x shadows, so substitution stops for x-bound occurrences
    -- Second binder: y, not equal to x, so substitution continues but needs shifting
    --
    -- Expected:
    --   bindings: domains unchanged (A0, B0)
    --   value:    occurrences of x0 inside value are shadowed → remain Var "x" 0
    --   cond:     y1 unaffected, but z would have been shifted under y;
    --             however z does not occur → unchanged.
    let actual   = substituteReplacement "x" 0 (Var "z" 0) r
        expected = ReplExpr bs (Var "x" 0) (Var "y" 1)

    actual `shouldBe` expected

substReplacementDomainSubstitution :: Assertion
substReplacementDomainSubstitution = do
    -- substitute x0 := y0 in:
    --   for a:(f x0), b:C . value = a0, cond = b1
    let bs = [("a", Apply (Var "f" 0) (Var "x" 0)), ("b", Var "C" 0)]
        r  = ReplExpr bs (Var "a" 0) (Var "b" 1)

    let actual   = substituteReplacement "x" 0 (Var "y" 0) r

    -- Expected:
    --   domain of a: f x0 → f y0
    --   domain of b: unchanged
    --   value, cond: no x0 present → unchanged
    let expected = ReplExpr
            [("a", Apply (Var "f" 0) (Var "y" 0)), ("b", Var "C" 0)]
            (Var "a" 0)
            (Var "b" 1)

    actual `shouldBe` expected

substReplacementShiftBinderNameCollision :: Assertion
substReplacementShiftBinderNameCollision = do
    -- binder: x:A
    -- value:  u0
    -- substitute x0 := x0 → this should become x1 under the binder
    let bs = [("x", Var "A" 0)]
        r  = ReplExpr bs (Var "u" 0) (Var "u" 0)

    let actual   = substituteReplacement "x" 0 (Var "x" 0) r
        expected =
            -- inserted expr lives under binder x, so must become x1
            ReplExpr bs (Var "u" 0) (Var "u" 0)

    -- Explanation:
    --   Domain does not contain x0 → unchanged.
    --   New expr shifts: x0 → x1.
    --   BUT since x is a binder, substitution must not apply inside value/cond
    --   because x shadows the target → value and cond remain unchanged.
    actual `shouldBe` expected

substReplacementDoubleShadow :: Assertion
substReplacementDoubleShadow = do
    -- { x_1 | x : A, x : B | x_2}
    let bs = [("x", Var "A" 0), ("x", Var "B" 0)]
        r = ReplExpr bs (Var "x" 1) (Var "x" 2)

        -- Substitute x :=_0 y0
        actual = substituteReplacement "x" 0 (Var "y" 0) r

        -- Notice that since we have two bindings for "x", the substitution of the free x at level 0 results in x2 being replaced by y0
        expected = ReplExpr bs (Var "x" 1) (Var "y" 0)

    actual `shouldBe` expected

substReplacementCaptureAvoidance :: Assertion
substReplacementCaptureAvoidance = do
    -- replacement: for x:A . value = x0, cond = t0
    -- substitute t0 := x0  (insertion contains binder variable, must be shifted)
    let bs = [("x", Var "A" 0)]
        r  = ReplExpr bs (Var "x" 0) (Var "t" 0)

    let actual   = substituteReplacement "t" 0 (Var "x" 0) r

    -- Expected:
    --   new expr shifts: x0 → x1
    --   binder x shadows substitution in value, so value stays x0
    --   cond: t0 replaced by x1
    let expected = ReplExpr bs (Var "x" 0) (Var "x" 1)

    actual `shouldBe` expected


betaReduceReplacementTest :: Assertion
betaReduceReplacementTest = do
    let bs = [("x", Lambda "a" (Var "a" 0))]
        r = ReplExpr bs (Apply (Lambda "b" (Var "b" 0)) (Var "z" 0)) (Var "c" 0)
        expected = ReplExpr bs (Var "z" 0) (Var "c" 0)
        actual = betaReduceReplacement r
    actual `shouldBe` expected


alphaReduceReplacementTest :: Assertion
alphaReduceReplacementTest = do
    let bs = [("x", Var "A" 0)]
        r = ReplExpr bs (Var "x" 0) (Var "B" 0)
        expected = ReplExpr [(defaultVarSymbol, Var "A" 0)] (Var defaultVarSymbol 0) (Var "B" 0)
        actual = alphaReduceReplacement r
    actual `shouldBe` expected
