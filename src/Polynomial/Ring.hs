{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Polynomial.Ring where

import Data.FiniteField.PrimeField
import GHC.TypeNats
import Data.Proxy
import Unsafe.Coerce (unsafeCoerce)

class (Num a, Eq a) => Ring a where -- really a GCD Domain
    (//) :: a -> a -> a
    (%)  :: a -> a -> a
    div_ :: a -> a -> (a,a)
    isUnit :: a -> Bool
    isZero :: a -> Bool

class Ring a => GCDD a where
    gcd_ :: a -> a -> a

class GCDD a => UFD a where
    factor_squarefree :: a -> (a, [a])
    squarefree :: a -> a

class UFD a => Field a where

class KnownNat p => Prime p where

instance KnownNat p => Prime p where

instance KnownNat p => Ring (PrimeField p) where
    (%) _ _ = 0
    (//) a b = a / b
    div_ a b = (a / b, 0)
    isUnit = (/=) 0
    isZero = (==) 0

instance KnownNat p => GCDD (PrimeField p) where
    gcd_ a b
        | a > b = a
        | otherwise = b

instance KnownNat p => UFD (PrimeField p) where
    factor_squarefree _ = undefined
    squarefree _ = undefined

instance Prime p => Field (PrimeField p) where


instance Ring Integer where
    (%) = mod
    (//) = div
    div_ = divMod
    isUnit 1 = True
    isUnit (-1) = True
    isUnit _ = False
    isZero = (==) 0

instance GCDD Integer where
    gcd_ = gcd


instance Ring Rational where
    (%) _ _ = 0
    (//) a b = a / b
    div_ a b = (a / b, 0)
    isUnit = (/=) 0
    isZero = (==) 0

instance GCDD Rational where
    gcd_ a b 
        | a > b = a
        | otherwise = b

instance UFD Rational where
    factor_squarefree a = (a, [])
    squarefree = id

instance Field Rational where


instance Ring Double where
    (%) _ _ = 0
    (//) a b = a / b
    div_ a b = (a / b, 0)
    isUnit = (/=) 0
    isZero = (==) 0

instance GCDD Double where
    gcd_ a b
        | a > b = a
        | otherwise = b

instance UFD Double where
    factor_squarefree a = (a, [])
    squarefree = id

instance Field Double where