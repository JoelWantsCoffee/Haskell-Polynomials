{-# LANGUAGE DataKinds, AllowAmbiguousTypes, ScopedTypeVariables #-}
module Hensel where

import Ring
import Polynomial
import Berlekamp

import Data.Proxy
import Data.FiniteField.PrimeField
import GHC.TypeNats
import Numeric.Natural
import Data.Reflection
import Data.List qualified as List

-- roots :: KnownNat p => Polynomial (PrimeField p) -> [ PrimeField p ]
-- roots =
--     (\p -> case p of
        
--     )
--     . (List.map )
--     . berlekamp 

-- inject :: Natural -> Polynomial Integer -> Polynomial (PrimeField SomeNat)
-- inject 

-- (poly p^k, poly p^k) -> (poly p^(k+1), poly p^(k+1))
-- gh + p^k (ag + bx) = gh
lift :: (KnownNat p, KnownNat k) => Polynomial Integer -> (Polynomial (PrimeField (p^k)), Polynomial (PrimeField (p^k))) -> (Polynomial (PrimeField (p^(k+1))), Polynomial (PrimeField (p^(k+1))))
lift = undefined 



hasMultipleRoots :: KnownNat p => Polynomial (PrimeField p) -> Bool
hasMultipleRoots p = (/=) (fromRing 1) (simplify $ gcd_ p (differentiate p))

-- performInField :: Natural -> Integer -> (forall p. KnownNat p => PrimeField p -> r) -> r
-- performInField p i f = 
--     reifyNat (fromIntegral p) 
--     $ \(_ :: Proxy p) -> f (fromInteger i :: PrimeField p)


-- data AnyPrimeField = AnyPrimeField (forall p. KnownNat p =>  PrimeField p)


factorInField :: Natural -> Polynomial Integer -> [ Polynomial Integer ]
factorInField n p = funcInField n p (fmap (fmap Data.FiniteField.PrimeField.toInteger) . factor)


funcInField :: Natural -> Polynomial Integer -> (forall (p :: Nat). KnownNat p => Polynomial (PrimeField p) -> r) -> r
funcInField n poly func = 
    reifyNat (fromIntegral n)
    $ \(_ :: Proxy a) -> func $ fmap (\i -> fromInteger i :: PrimeField a) poly

    -- reifyNat (fromIntegral n)
    -- $ \(_ :: Proxy pp) -> f 
    -- $ fmap (fromInteger :: (Integer -> PrimeField pp)) p

-- map :: KnownNat p => (PrimeField p -> PrimeField p) -> AnyPrimeField -> AnyPrimeField
-- map f (AnyPrimeField a) = AnyPrimeField $ f a

-- applyMod :: Integer -> Integer -> AnyPrimeField
-- applyMod prime i = 

-- withKnownNat :: Natural -> (forall p. KnownNat p => r) -> r
-- withKnownNat n f = reifyNat (fromIntegral n) (const f)

-- reifyNat :: forall r. Integer -> (forall (n :: Nat). KnownNat n => Proxy n -> r) -> r


-- proxyToPrimeField :: KnownNat p => Integer -> Proxy p -> PrimeField p
-- proxyToPrimeField i _ = (fromIntegral i)


-- extract :: KnownNat p => AnyPrimeField -> PrimeField p
-- extract (AnyPrimeField i) = i

-- applyMod_ :: KnownNat p => (PrimeField p) -> Polynomial Integer -> Polynomial (PrimeField p)
-- applyMod_ p f = (fmap (fromIntegral) f)

-- applyMod3 = applyMod_ ( 0 :: PrimeField 3 )
-- applyMod5 = applyMod_ ( 0 :: PrimeField 5 )
-- applyMod7 = applyMod_ ( 0 :: PrimeField 7 )
-- applyMod11 = applyMod_ ( 0 :: PrimeField 11 )
-- applyMod13 = applyMod_ ( 0 :: PrimeField 13 )
-- applyMod17 = applyMod_ ( 0 :: PrimeField 17 )
-- applyMod19 = applyMod_ ( 0 :: PrimeField 19 )