{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Polynomial.Ring 
    ( Ring(..)
    , GCDD(..)
    , UFD(..)
    , Field(..)
    , Prime
    , Pow
    , PrimeField
    , FiniteCyclicRing
    , KnownPrime
    , AssumePrime
    , reifyPrime
    , primeVal
    , toFiniteCyclicRing
    ) where

import Data.FiniteField.PrimeField qualified as PF
import GHC.TypeNats
import Data.Reflection
import Data.Proxy

class (Num a, Ord a, Eq a) => Ring a where
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


-- INTEGER QUOTIENT RINGS 

type FiniteCyclicRing (n :: Nat) = PF.PrimeField n

instance KnownNat p => Ring (FiniteCyclicRing p) where
    (%) _ _ = 0
    (//) a b = a / b
    div_ a b = (a / b, 0)
    isUnit = (/=) 0
    isZero = (==) 0

instance KnownNat p => GCDD (FiniteCyclicRing p) where
    gcd_ a b
        | a > b = a
        | otherwise = b

instance KnownNat p => UFD (FiniteCyclicRing p) where
    factor_squarefree _ = undefined
    squarefree _ = undefined


-- PRIME STUFF


data Prime (n :: Nat)

type family AssumePrime (n :: Nat) :: Prime n

type family Pow (p :: Prime n) (k :: Nat) :: Nat where
    Pow (p :: Prime n) k = n ^ k

newtype PrimeField (p :: Prime n) = PrimeField (FiniteCyclicRing n)
      deriving (Eq, Ord, Num, Ring, GCDD, UFD, Fractional, Bounded, Enum)

instance KnownPrime p => Show (PrimeField p) where
    show (PrimeField e) = show e

toFiniteCyclicRing :: forall (n :: Nat) (p :: Prime n). PrimeField p -> FiniteCyclicRing n
toFiniteCyclicRing (PrimeField n) = n

class KnownNat n => KnownPrime (p :: Prime n) where
    primeVal :: Proxy p -> Natural

instance KnownNat n => KnownPrime (p :: Prime n) where
    primeVal (_ :: Proxy p) = natVal $ Proxy @n

reifyPrime :: forall r. Integer -> (forall (n :: Nat) (p :: Prime n). KnownPrime p => Proxy p -> r) -> r
reifyPrime i f = reifyNat i (f . assumePrime)

assumePrime :: forall (n :: Nat) (p :: Prime n) . (KnownNat n, KnownPrime p) => Proxy n -> Proxy p
assumePrime Proxy = Proxy

instance KnownPrime p => Field (PrimeField p) where