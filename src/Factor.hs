{-# LANGUAGE DataKinds #-}

module Factor where

import Polynomial.Berlekamp
import Polynomial.Polynomial
import Polynomial.Ring
import Polynomial.Squarefree
import Polynomial.Hensel
import Data.FiniteField.PrimeField qualified as PF
import GHC.TypeNats


aa :: Polynomial Integer
aa = (+) (monomial  1 3) ((+) (monomial  (-2) 2) (monomial  (-4) 0))
bb :: Polynomial Integer
bb = (+) (monomial  1 1) (monomial  (-3) 0)

a :: Polynomial Rational
a = (+) (monomial 1 3) ((+) (monomial (-2) 2) (monomial  (-4) 0))
b :: Polynomial Rational
b = (+) (monomial 1 1) (monomial (-3) 0)
-- c :: Polynomial Rational
-- c = gcd_ a b

d :: Polynomial Integer
d = (monomial 15 0)

e :: Polynomial Integer
e = (monomial 9 0)

-- x :: Polynomial Rational
-- x = (monomial 1 1) * (monomial 3 0)
-- f :: Polynomial Rational
-- f = expand $ x * x
-- f' :: Polynomial Rational
-- f' = differentiate f

-- g :: Polynomial Rational
-- g = expand $ (*) ((+) (monomial 1 1) (monomial 1 0)) ((+) (monomial 1 2) (monomial 1 0))

gg :: Polynomial Integer
gg = expand $ (*) ((+) (monomial 1 1) (monomial 1 0)) ((+) (monomial 1 2) (monomial 1 0))

ggg :: Polynomial (PrimeField (p :: Prime 13))
ggg = expand $ (*) ((+) (monomial 1 1) (monomial 1 0)) ((+) (monomial 1 2) (monomial 1 0))

-- fac1 = expand $ (monomial 1 1) + (monomial 5 0) :: Polynomial Integer

-- g' :: Polynomial Rational
-- g' = differentiate g
-- p :: Polynomial Rational
-- p = (*) f a 

hh :: Polynomial Integer
hh = (+) ((+) (monomial 1 4) (monomial (-1) 2)) ((+) (monomial (-1) 1) (monomial (-1) 0))

hhh :: Polynomial (PrimeField (p :: Prime 13))
hhh = (+) ((+) (monomial 1 4) (monomial (-1) 2)) ((+) (monomial (-1) 1) (monomial (-1) 0))

-- f = hh
-- out = recombine @(7^3) f $ expand <$> liftN2 @7 @3 f
-- out = expand <$> (fmap (fromInteger :: Integer -> PrimeField (7^2))) <$> [g', h']



-- test :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
-- test = \polynom -> [expand $ foldr (*) 1 (berlekamp polynom), expand $ squareFree polynom]

x :: Ring r => Polynomial r
x = monomial 1 1