module Test.Unit where


import Test.Tasty
import Test.Tasty.HUnit
import Test.Unit.Nominal qualified as Nominal
import Test.Unit.Symdiff qualified as Symdiff
import Test.Unit.Syntax qualified as Syntax

unitTests :: TestTree
unitTests = testGroup "unit tests"
    [testCase "filter" filtersWell
    , Syntax.unitTests  -- include the Syntax.DeBruijn tests
    , Nominal.unitTests
    ]


filtersWell :: Assertion
filtersWell = do
    assertBool "Filter works on symdiff problem" Symdiff.filtersWell
