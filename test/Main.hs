{-# LANGUAGE DataKinds #-}

module Main (main) where

import Polynomial.Factor
import Polynomial.Polynomial
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.List as List
import Data.Maybe (fromMaybe)

main :: IO ()
main = defaultMain tests

assertFactoring :: forall r. (Show r, Ord r, GCDD r, ED r, UFD (Polynomial r)) => (Polynomial r) -> [Polynomial r] -> Assertion
assertFactoring p lst = assertEqual errorMessage expected actual
  where
    actual = List.sort $ fmap expand . fromMaybe [] . fmap listify . factor $ p
    expected = List.sort $ expand <$> lst
    errorMessage = "Failed to factor: " ++ show (expand p)


tests :: TestTree
tests = testGroup "Tests"
    [ testCase "Simple factorisation" testSimpleFactor
    , testCase "More factorisation tests" testMoreFactors
    -- , testCase "Even More factorisation tests" testEvenMore
    ]

testSimpleFactor :: Assertion
testSimpleFactor = do
    assertFactoring @Integer x [x]
    assertFactoring @(PrimeField (AssumePrime 7)) x [x]
    assertFactoring @Integer (2 * x * x) [2, x]

testMoreFactors :: Assertion
testMoreFactors = do
    -- Tests for Integer
    assertFactoring @Integer (x^3 - 1) [x - 1, x^2 + x + 1]
    assertFactoring @Integer (x^2 - 1) [x - 1, x + 1]
    assertFactoring @Integer (x^2 - 2*x + 1) [x - 1]
    assertFactoring @Integer (x^4 - 1) [x - 1, x + 1, x^2 + 1]
    assertFactoring @Integer (x^5 - x^4 + x^3 - x^2 + x - 1) [x - 1, x^2 - x + 1, x^2 + x + 1]
    assertFactoring @Integer (x^4 + 2*x^3 + x^2) [x, x + 1]
    assertFactoring @Integer (x^6 - 1) [x - 1, x + 1, x^2 - x + 1, x^2 + x + 1]
    assertFactoring @Integer (x^7 - x) [x, x - 1, x + 1, x^2 - x + 1, x^2 + x + 1]

testEvenMore :: Assertion
testEvenMore = do
    assertFactoring @Integer (x^3 - x^2 - x + 1) [x - 1, x + 1]
    assertFactoring @Integer (x^3 - x^2 + x - 1) [x - 1, x^2 + 1]
    assertFactoring @Integer (x^4 - 2*x^3 + 3*x^2 - 2*x + 1) [x^2 - x + 1, x^2 - x + 1]
    assertFactoring @Integer (x^3 + x^2 - x - 1) [x + 1, x^2 - 1]
    assertFactoring @Integer (x^4 + x^3 - x - 1) [x^2 + x + 1, x^2 - 1]
