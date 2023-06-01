module Squarefree where

import Polynomial
import Ring

-- yun :: Polynomial -> Polynomial
-- yun p 
--     | degree p == 0 = p
--     | otherwise = let
--         dp = differentiate p
--         gcd = gcd_ p dp
--         (sqff, _) = divide p gcd
--         sqffgcd = gcd_ sqff dp
--         (sqffpart, _) = divide sqff sqffgcd
--         (rest, _) = divide gcd sqffgcd
--         in
--         Sum sqffpart (yun rest)

yun2 :: Ring r => Polynomial r -> Polynomial r -> Polynomial r
yun2 b d
    | degree b == 0 = b
    | otherwise = let
        a = gcd_ b d
        (b', _) = b `divide` a
        (c, _) = d `divide` a
        d' = c `subtract_` differentiate b'
        in
        a * (yun2 b' d')

type Factors r = (Polynomial r, Integer)
            
yun :: Ring r => Integer -> Polynomial r -> Polynomial r -> [Factors r]
yun i b d
    | degree b == 0 = [(b, i)]
    | otherwise = let
        a = gcd_ b d
        b' = b // a
        c = d // a
        d' = c - differentiate b'
        in
        (a, i) : yun (i + 1) b' d'


undo :: Ring r => [Factors r] -> Polynomial r
undo = foldr (\(a, i) b -> pow a i * b) (Monomial 1 0)

forgetPowers :: Ring r => [Factors r] -> Polynomial r
forgetPowers = foldr (\(a, _) b -> a * b) (Monomial 1 0)

sqfr :: Ring r => Polynomial r -> Polynomial r
sqfr = forgetPowers . decompose

decompose :: Ring r => Polynomial r -> [Factors r]
decompose f
    | isConstant f = []
    | otherwise    = yun 1 b $ (f' // a0) - (differentiate b)
    where
        f' = differentiate f
        a0 = gcd_ f f'
        b = f // a0

squareFree :: Ring r => Polynomial r -> Polynomial r
squareFree f
    | (simplify f) == 1 = 1
    | otherwise = let g = gcd_ f (differentiate f)
                      h = f // g
                  in if isZero (g // h) 
                    then f
                    else h * squareFree (g // h)

simp :: Ring r => Polynomial r -> Polynomial r
simp = simplify

ddx :: Ring r => Polynomial r -> Polynomial r
ddx = differentiate