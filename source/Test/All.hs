module Test.All where


import Base
import Test.Golden
import Test.Unit
import Test.Tasty


runTests :: IO ()
runTests = defaultMain =<< tests

tests :: IO TestTree
tests = testGroup "all tests" <$> sequence [goldenTests, return unitTests]
