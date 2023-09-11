{-# LANGUAGE DataKinds #-}

module Polynomial.Factor 
    ( Ring(..)
    , GCDD(..)
    , UFD(..)
    , ED(..)
    , Field(..)
    , Prime
    , KnownPrime
    , PrimeField
    , FiniteCyclicRing
    , primeVal
    , factor
    , listify
    , unfactor
    , x
    )
where

import Polynomial.Polynomial
import Polynomial.Ring
import Polynomial.Squarefree()
import Polynomial.Berlekamp()
import Polynomial.Hensel()

import GHC.Natural (Natural)
import Data.List as List

newtype Factoring a = Factoring (a, [(a, Natural)])

instance Show a => Show (Factoring a) where
    show (Factoring (u, lst)) = foldr1 (\a b -> a ++ " * " ++ b) $ (show u) : ((
            \(p, n) -> if (n == 1) then "(" ++ (show p) ++ ")" else "(" ++ (show p) ++ ")^" ++ (show n)
        ) <$> lst)

unfactor :: Ring r => Factoring r -> r
unfactor (Factoring (r,lst)) = (*) r $ foldl (*) 1 ((\(p, e) -> p ^ e) <$> lst)

listify :: Ring r => Factoring (Polynomial r) -> [(Polynomial r)]
listify (Factoring (_, lst)) = (expand . fst) <$> lst

factor :: (ED r, UFD (Polynomial r)) => Polynomial r -> Maybe (Factoring (Polynomial r))
factor p =
    fmap Factoring 
    -- $ Just  
    $ (\(a,l) -> 
        if (not $ foldr (\t -> (&&) (irreducible $ fst t)) True l) then
            Nothing
        else if (isUnit a) then
            Just (a,l) 
        else if (degree a == 0) || (irreducible a) then
            Just (1, (a,1):l) 
        else
            Nothing
      )
    $ (\(u,lst) -> (u, List.reverse $ List.sort $ List.filter ((<) 0 . snd) lst))
    $ foldr (\fact (rest, lst) -> (\(r,l) -> (expand r, l:lst)) $ recover_power rest (fact, 0)) (p, []) factors
    where
        recover_power :: ED r => Polynomial r -> (Polynomial r, Natural) -> (Polynomial r, (Polynomial r, Natural))
        recover_power base (fact, power) = if (isZero . snd $ polyDivMod base fact) then recover_power (base /. fact) (fact, power + 1) else (base, (fact, power))

        (_, factors) = factor_squarefree . snd . purePart $ squarefree p

        -- use primitive part instead of pure part
        -- https://wiki.haskell.org/Literate_programming

x :: Ring r => Polynomial r
x = monomial 1 1