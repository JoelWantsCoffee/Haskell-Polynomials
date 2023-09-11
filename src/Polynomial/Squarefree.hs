module Polynomial.Squarefree 
    ( squarefree_field
    , decompose
    ) where
    

import Polynomial.Polynomial
import Polynomial.Ring

            
yun :: Field r => Integer -> Polynomial r -> Polynomial r -> [(Polynomial r, Integer)]
yun i b d
    | degree b == 0 = [(b, i)]
    | otherwise = let
        a = gcd_ b d
        b' = b // a
        c = d // a
        d' = c - differentiate b'
        in
        (a, i) : yun (i + 1) b' d'

-- undo :: Ring r => [(Polynomial r, Integer)] -> Polynomial r
-- undo = foldr (\(a, i) b -> a^i * b) (monomial 1 0)

forgetPowers :: Ring r => [(Polynomial r, Integer)] -> Polynomial r
forgetPowers = foldr (\(a, _) b -> a * b) (monomial 1 0)

squarefree_field :: Field r => Polynomial r -> Polynomial r
squarefree_field = forgetPowers . decompose

decompose :: Field r => Polynomial r -> [(Polynomial r, Integer)]
decompose f
    | degree f == 0 = []
    | otherwise    = yun 1 b $ (f' // a0) - (differentiate b)
    where
        f' = differentiate f
        a0 = gcd_ f f'
        b = f // a0