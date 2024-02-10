module Test.Unit where


import Test.Tasty
import Test.Tasty.HUnit
import Test.Unit.Symdiff qualified as Symdiff


unitTests :: TestTree
unitTests = testGroup "unit tests" [testCase "filter" filtersWell]


filtersWell :: Assertion
filtersWell = do
    assertBool "Filter works on symdiff problem" Symdiff.filtersWell
