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
    [ testCase "Simple factorization" testSimpleFactor
    , testCase "More factorization tests" testMoreFactors
    ]

testSimpleFactor :: Assertion
testSimpleFactor = do
    assertFactoring @Integer x [x]
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

    -- Tests for Rational
    -- assertFactoring @Rational ((x^3) - 1//4) [x^3 - 1//4]
    -- assertFactoring @Rational ((x^2) - 1//9) [x - 1//3, x + 1//3]
    -- assertFactoring @Rational (4*x^2 - 1) [2*x - 1, 2*x + 1]
    -- assertFactoring @Rational ((x^3) - (3//2)*(x^2) + (3//4)*x - 1//8) [(x - 1//2)^3]
    -- assertFactoring @Rational ((x^5) - 1//16) [x^5 - 1//16]
    -- assertFactoring @Rational ((x^4) - (2//3)*(x^3) + (1//3)*(x^2)) [x, x^2 - 2//3*x + 1//3]
    -- assertFactoring @Rational ((x^6) - 1//27) [x^2 - 1//3, x^4 + (x^2)//3 + 1//9]
    -- assertFactoring @Rational ((x^4) + (x^3)//2 + (x^2)//4) [x, x^2 + x//2 + 1//4]
    -- assertFactoring @Rational ((x^5) - (x^4)//2 + (x^3)//4 - (x^2)//8 + x//16 - 1//32) [x - 1//2, x^2 - x//2 + 1//4, x^2 + x//2 + 1//4]