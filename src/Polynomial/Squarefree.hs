module Polynomial.Squarefree 
    ( squarefree_field
    , pure_part
    , factor
    , decompose
    ) where
    

import Polynomial.Polynomial
import Polynomial.Ring
import GHC.Natural (Natural)
import Data.List as List

            
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

newtype Factoring a = Factoring (a, [(a, Natural)])

instance Show a => Show (Factoring a) where
    show (Factoring (u, lst)) = foldr1 (\a b -> a ++ " * " ++ b) $ (show u) : ((
            \(p, n) -> if (n == 1) then "(" ++ (show p) ++ ")" else "(" ++ (show p) ++ ")^" ++ (show n)
        ) <$> lst)

factor :: (GCDD r, UFD (Polynomial r)) => Polynomial r -> Factoring (Polynomial r)
factor p = Factoring 
    $ (\(u,lst) -> (u, List.reverse $ List.sort lst))   
    $ foldr (\fact (rest, lst) -> (\(r,l) -> (expand r, l:lst)) 
    $ recover_power rest (fact, 0)) (p, []) factors
    where
        recover_power :: Ring r => Polynomial r -> (Polynomial r, Natural) -> (Polynomial r, (Polynomial r, Natural))
        recover_power base (fact, power) = if isZero remainder then recover_power quotient (fact, power + 1) else (base, (fact, power))
            where (quotient, remainder) = base `div_` fact

        (_, factors) = factor_squarefree $ pure_part $ squarefree p

pure_part :: GCDD r => Polynomial r -> Polynomial r
pure_part p = (//) p $ flip monomial 0 . foldr1 gcd_ . fmap fst . toList $ p