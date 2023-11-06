{-# LANGUAGE MonoLocalBinds #-}
module Polynomial.Berlekamp (berlekamp) where

import Polynomial.Squarefree
import Polynomial.Polynomial
import Polynomial.Ring
import Polynomial.CustomMatrix

import Data.Matrix (Matrix, fromLists, toLists, identity, rref, (<|>), nrows)
import Data.Either.Combinators qualified as Either
import Data.List
import GHC.TypeNats()
import Data.Proxy

unvector :: Ring r => [r] -> Polynomial r
unvector lst =
    expand
    $ foldr (+) 0
    $ zipWith monomial (reverse lst) [0 ..]

vector :: Ring r => Natural -> Polynomial r -> [r]
vector n p = fmap ( flip coeff p ) ( reverse [ 0 .. n ] )

everyVector :: forall p. KnownPrime p => Integer -> [[PrimeField p]]
everyVector i
  | i == 1 = map singleton field
  | otherwise = [ x:v | v <- everyVector (i - 1), x <- field ]
  where
    field = map fromIntegral [1 .. p]
    p = primeVal (Proxy @p)

nullspace :: forall p. KnownPrime p => [[PrimeField p]] -> [[PrimeField p]]
nullspace mat = filter (all (== 0) . multiply mat) (everyVector (fromIntegral $ length mat))

-- basis :: Field f => [[f]] -> [[f]]
-- basis lst = gramSchmidt $ filter (not . all (== 0)) lst

matrixFromLinearFunction :: Ring r => Integer -> ([r] -> [r]) -> [[r]]
matrixFromLinearFunction d f = transpose [ f [ if (i == j) then 1 else 0 | i <- [0 .. d - 1] ] | j <- [0 .. d - 1] ]

berlekampMatrix :: forall p. KnownPrime p => Polynomial (PrimeField p) -> [[ PrimeField p ]]
berlekampMatrix f = toLists $ q_f - i
  where
    q_f = fromLists $ matrixFromLinearFunction (fromIntegral n) (vector (n - 1) . (% f) . (^ p) . unvector)
    i = identity (fromIntegral n)

    n = degree f
    p = primeVal (Proxy :: Proxy p)

berlekamp :: forall p. KnownPrime p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
berlekamp f_
  | isZeroOrUnit f = []
  | irreducible f = [f]
  | otherwise = 
    concatMap berlekamp
    . ( \h -> [ gcd_ (f) (h - c) | c <- field ] )
    . head
    . filter ( not . isZeroOrUnit )
    . map ( monic . unvector )
    . nullspace
    $ berlekampMatrix f
  where
    field = map fromIntegral [1 .. p]
    monic = expand . snd . primitivePart
    isZeroOrUnit = \h -> (isUnit h) || (h == 0)
    p = primeVal (Proxy :: Proxy p)
    f = expand $ squarefree f_


instance (KnownPrime p) => UFD (Polynomial (PrimeField p)) where
  factor_squarefree = (\(u, p) -> (monomial u 0, berlekamp p)) . coercemonic 
  squarefree = squarefree_field
  irreducible p | monic == 0 = False
                | isUnit monic = False
                | (squarefree_field monic) /= monic = False
                | otherwise = length (nullspaceBasis $ berlekampMatrix monic) == 1
              where
                monic = p // (monomial (leadingCoeff p) 0)