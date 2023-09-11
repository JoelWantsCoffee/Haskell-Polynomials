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
    , ED(..)
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

type NonZero a = a



{-  DEFINITIONS

    (/.) : a -> b -> q
        such that a = q * b, if such a q exists,
        otherwise behaviour is undefined

    (isUnit) : a -> Bool
        returns true if some a^(-1) exists such
        that a * a^(-1) = 1. Otherwise returns false
    
    (isZero) : a -> Bool
        returns true if forall b, a + b = b + a = b
        otherwise returns false
    
-}
class (Num a, Ord a, Eq a) => Ring a where
    (/.) :: a -> NonZero a -> a 
    isUnit :: a -> Bool
    isZero :: a -> Bool

{-  DEFINITIONS

    gcd_ : a -> b -> d
        returns d, m such that d|a and d|b, and if
        for some c, c|a and c|b then c|d

-}
class Ring a => GCDD a where
    gcd_ :: a -> a -> a

{-  DEFINITIONS

    factor_squarefree : a -> (u, lst)
        if a is squarefree return some unit u and
        list of irreducibles lst sucht that 
        a = fold (*) u lst, otherwise behaviour is
        undefined.

    squarefree : a -> b
        returns b equal to a with any squares removed

-}
class GCDD a => UFD a where
    factor_squarefree :: a -> (a, [a])
    squarefree :: a -> a
    irreducible :: a -> Bool

{-  DEFINITIONS

    div_ :: a -> a -> (a,a)
    (//) :: a -> a -> a
    (%) :: a -> a -> a
    euclidean :: a -> Integer
        euclidean division.
-}
class GCDD a => ED a where
    (//) :: a -> a -> a
    (//) = (/.)
    (%) :: a -> a -> a
    euclidean :: a -> Integer
    div_ :: a -> a -> (a,a)
    div_ a b = (a // b, a % b) 


{-  DEFINITIONS

    inv : a -> b
        for any non-zero a return b such that a * b = 1
-}
class ED a => Field a where
    inv :: a -> a
    inv = (//) 1

{-  PROOFS

    # all given by ghc #

-}
instance Ring Integer where
    (/.) a b = (\(q,r) -> if r == 0 then q else 0) $ divMod a b
    isUnit 1 = True
    isUnit (-1) = True
    isUnit _ = False
    isZero = (==) 0

{-  PROOFS

    # all given by ghc #
    
-}
instance GCDD Integer where
    gcd_ = gcd

{-  PROOFS

    # not implemented #
    
-}
instance UFD Integer where
    factor_squarefree = undefined
    squarefree = undefined
    irreducible i   | isZero i  = False
                    | isUnit i  = False
                    | i > 1     = null [ x | x <- [2 .. floor (sqrt (fromIntegral i :: Double))], i `mod` x == 0 ]
                    | otherwise = irreducible (-i)


{-  PROOFS

    # all given by ghc #
    
-}
instance ED Integer where
    (//) = div
    (%) = mod
    div_ = divMod
    euclidean = id


{-  PROOFS

    # all given by ghc #
    
-}
instance Ring Rational where
    (/.) = (/)
    isUnit = (/=) 0
    isZero = (==) 0


{-  PROOFS

    # all given by ghc #
    
-}
instance GCDD Rational where
    gcd_ a _ = a

{-  PROOFS

    # all given by ghc #
    
-}
instance ED Rational where
    (%) 0 b = b
    (%) _ _ = 0
    euclidean _ = 0

{-  PROOFS

    # all given by ghc #
    
-}
instance UFD Rational where
    factor_squarefree a = (a, [])
    squarefree = id
    irreducible _ = False 

{-  PROOFS

    # all given by ghc #
    
-}
instance Field Rational


-- INTEGER QUOTIENT RINGS 

type FiniteCyclicRing (n :: Nat) = PF.PrimeField n

{-  PROOFS

    # all given by ghc #
    
-}
instance KnownNat p => Ring (FiniteCyclicRing p) where
    (/.) = (/)
    isUnit = (/=) 0
    isZero = (==) 0

{-  PROOFS

    # all given by ghc #
    
-}
instance KnownNat p => GCDD (FiniteCyclicRing p) where
    gcd_ a 0 = a
    gcd_ a b = gcd_ a (a % b)

{-  PROOFS

    # all given by ghc #
    
-}
instance KnownNat p => ED (FiniteCyclicRing p) where
    (//) = (/)
    (%) 0 _ = 0
    (%) a b 
        | gcd (fromIntegral $ natVal (Proxy :: Proxy p)) (PF.toInteger b) == 1 = 0
        | otherwise = a - b * (a // b)
    euclidean = PF.toInteger

{-  PROOFS

    # not implemented #
    
-}
instance KnownNat p => UFD (FiniteCyclicRing p) where
    factor_squarefree _ = undefined
    squarefree _ = undefined
    irreducible _ = False


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

instance KnownPrime p => ED (PrimeField p) where
    (%) 0 b = b
    (%) _ _ = 0
    euclidean _ = 0

instance KnownPrime p => Field (PrimeField p)