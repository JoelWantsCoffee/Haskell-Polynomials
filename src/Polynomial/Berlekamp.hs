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

-- gaussian_elimination :: Field a => [[a]] -> [[a]]
-- gaussian_elimination matrix = undefined
--   where
--     go lead 

--     rows mat = genericLength mat
--     cols mat = genericLength (head mat)

--     swap_rows :: Field a => Int -> Int -> [[a]] -> [[a]]
--     swap_rows i j mat = [ mat!!(swap r) | r <- [0..(rows mat - 1)] ]
--       where
--         swap r 
--           | r == i = j
--           | r == j = i
--           | otherwise = r

--     scale_row :: Field a => Int -> a -> [[a]] -> [[a]]
--     scale_row i scalar mat = [ if (r == i) then map (* scalar) (mat!!i) else mat!!r | r <- [0..(rows mat - 1)] ]

--     add_scaled_row :: Field a =>  Int -> Int -> a -> [[a]] -> [[a]]
--     add_scaled_row i j scalar mat = [ if (r == i) then zipWith (\a b -> a + scalar * b) (mat!!i) (mat!!j) else mat!!r | r <- [0..(rows mat - 1)] ]

-- find_basis :: Field a => [[a]] -> [[a]]
-- find_basis lst = filter ( not . all (== 0) ) $ gaussian_elimination lst

matrixFromLinearFunction :: Ring r => Integer -> ([r] -> [r]) -> [[r]]
matrixFromLinearFunction d f = transpose [ f [ if (i == j) then 1 else 0 | i <- [0 .. d - 1] ] | j <- [0 .. d - 1] ]

normalise :: Field a => [a] -> [a]
normalise lst 
  | all (== 0) lst = lst
  | otherwise = map (* inv (head $ filter (/= 0) lst)) lst

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
                | otherwise = length ( nub $ map normalise $ filter ( not . all (== 0) ) $ nullspace $ berlekampMatrix monic) == 1
              where
                monic = p // (monomial (leadingCoeff p) 0)