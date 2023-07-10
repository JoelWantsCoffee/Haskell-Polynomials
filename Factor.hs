{-# LANGUAGE DataKinds #-}
import Berlekamp
import Polynomial
import Ring
import Squarefree
import Hensel
import Data.FiniteField.PrimeField
import GHC.TypeNats


aa :: Polynomial Integer
aa = Sum (Monomial  1 3) (Sum (Monomial  (-2) 2) (Monomial  (-4) 0))
bb :: Polynomial Integer
bb = Sum (Monomial  1 1) (Monomial  (-3) 0)

a :: Polynomial Rational
a = Sum (Monomial 1 3) (Sum (Monomial (-2) 2) (Monomial  (-4) 0))
b :: Polynomial Rational
b = Sum (Monomial 1 1) (Monomial (-3) 0)
-- c :: Polynomial Rational
-- c = gcd_ a b

d :: Polynomial Integer
d = (Monomial 15 0)

e :: Polynomial Integer
e = (Monomial 9 0)

x = Monomial 1 1

-- x :: Polynomial Rational
-- x = (Monomial 1 1) * (Monomial 3 0)
-- f :: Polynomial Rational
-- f = simplify $ x * x
-- f' :: Polynomial Rational
-- f' = differentiate f

g :: Polynomial Rational
g = simplify $ Product (Sum (Monomial 1 1) (Monomial 1 0)) (Sum (Monomial 1 2) (Monomial 1 0))

gg :: Polynomial Integer
gg = simplify $ Product (Sum (Monomial 1 1) (Monomial 1 0)) (Sum (Monomial 1 2) (Monomial 1 0))

ggg :: Polynomial (PrimeField 13)
ggg = simplify $ Product (Sum (Monomial 1 1) (Monomial 1 0)) (Sum (Monomial 1 2) (Monomial 1 0))

fac1 = simplify $ (Monomial 1 1) + (Monomial 5 0) :: Polynomial Integer

-- g' :: Polynomial Rational
-- g' = differentiate g
-- p :: Polynomial Rational
-- p = Product f a 

hh :: Polynomial Integer
hh = Sum (Sum (Monomial 1 4) (Monomial (-1) 2)) (Sum (Monomial (-1) 1) (Monomial (-1) 0))

hhh :: Polynomial (PrimeField 7)
hhh = Sum (Sum (Monomial 1 4) (Monomial (-1) 2)) (Sum (Monomial (-1) 1) (Monomial (-1) 0))

-- k = simplify (Sum a f)


test :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
test = \polynom -> [simplify $ foldr (*) 1 (berlekamp polynom), simplify $ squareFree polynom]