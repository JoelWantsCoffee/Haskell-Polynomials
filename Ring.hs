{-# LANGUAGE DataKinds #-}

module Ring where

import Data.FiniteField.PrimeField
import GHC.TypeNats

class (Num a, Eq a) => Ring a where -- really a GCD Domain
    (//) :: a -> a -> a
    (%)  :: a -> a -> a
    div_ :: a -> a -> (a,a)
    gcd_ :: a -> a -> a
    isUnit :: a -> Bool

class Factorable a where
    factor :: a -> [a]

instance KnownNat p => Ring (PrimeField p) where
    (%) a b = 0
    (//) a b = a / b
    gcd_ a b
        | a > b = a
        | otherwise = b
    div_ a b = (a / b, 0)
    isUnit = (/=) 0

instance Ring Rational where
    (%) a b = 0
    (//) a b = a / b
    div_ a b = (a / b, 0)
    gcd_ a b 
        | a > b = a
        | otherwise = b
    isUnit = (/=) 0

instance Ring Integer where
    (%) = mod
    (//) = div
    div_ = divMod
    gcd_ = gcd
    isUnit 1 = True
    isUnit (-1) = True
    isUnit _ = False