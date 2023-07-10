{-# LANGUAGE DataKinds, AllowAmbiguousTypes, ScopedTypeVariables, TypeFamilies #-}
module Hensel where

import Ring
import Polynomial
import Berlekamp

import Data.Proxy
import Data.FiniteField.PrimeField as PrimeField
import GHC.TypeNats
import Numeric.Natural
import Data.Reflection
import Data.List qualified as List
import Combinatorics qualified as Combinatorics

toIntegerCoeff :: KnownNat p => Polynomial (PrimeField p) -> Polynomial Integer
toIntegerCoeff = fmap (PrimeField.toInteger)

toPrimeFieldCoeff :: forall p. KnownNat p => Proxy p -> Polynomial Integer -> Polynomial (PrimeField p)
toPrimeFieldCoeff _ = fmap (fromIntegral)

cursed :: KnownNat p => [Polynomial (PrimeField p)] -> (Polynomial (PrimeField p), Polynomial (PrimeField p))
cursed lst = (lst!!0, lst!!1)   

extendedGcd :: Ring r => r -> r -> (r,r,r) 
extendedGcd a b | isZero b = (1, 0, a)
                | otherwise = 
                    let (q, r) = a `div_` b
                        (s, t, g) = extendedGcd b r
                    in (t, s - q * t, g)


{- hensel's lemma

Suppose f(x) in Z[x] 
    and f (a) =  0 mod p^m
    and f'(a) != 0 mod p^m

Then there is a unique t in {0,1,...,p-1} such that
    f(a + tp^m) = 0 mod p^{m+1}


proof:

set n = deg(f), expand f(x) as a taylor series at x = a.
    f(x) = f(a) + f'(a)(x-a) + f''(a)/2! (x-a)^2 + ... + f^(n)(a)/n! (x-a)^n

evaluate at x = tp^m + a

f(a + tp^m) = f(a) + f'(a)tp^m + ... + f^(n)(a)/n! * t^n * p^mn

observe f^(k)(a) / k! in Z.

f(a + tp^m) === f(a) + f'(a)tp^m (mod p^{m+1})
            === 0 (mod p^{m+1}) (want this)

f'(a) t p^m === - f(a) (mod p^{m+1}) 

divide all sides by p^m, f(a) does divide it -- see assumptions

<=>

f'(a)t === -f(a) / p^m (mod p)


t === (- f(a) / p^m) / (f'(a)) (mod p)

find solve this equation to find t.



-}


lift :: forall (p :: Nat) (k :: Nat). (KnownNat p, KnownNat k)
    => Polynomial Integer
    -> Integer
    -> Integer
lift f a = fromIntegral $ a + t * (p^k)
    where
        p = fromIntegral $ natVal (Proxy :: Proxy p)
        k = fromIntegral $ natVal (Proxy :: Proxy k)
        
        dfa = fromIntegral (evaluate a $ differentiate f) :: PrimeField p
        _fa_pm = fromIntegral (- (evaluate a f) // (p^k)) :: PrimeField p

        t = PrimeField.toInteger $ _fa_pm // dfa

-- The-art-of-computer-programming.-Vol.2.-Seminumerical-algorithms-by-Knuth-Donald PAGE 452 F2
recombine :: KnownNat m => [Polynomial (PrimeField m)] -> [Polynomial (Integer)]
recombine = recombine_ 1

recombine_ :: KnownNat m => Integer -> [Polynomial (PrimeField m)] -> [Polynomial (Integer)]
recombine_ d polys = undefined
    where
        choices = Combinatorics.tuples (fromInteger d) polys


--  _ f_ (g_,h_) = (simplify $ g + (simplify a_) * scale * pk, simplify $ h + (simplify b_) * scale * pk)
--     where
--         pk = fromRing . fromIntegral . natVal $ (Proxy :: Proxy (p^k))
--         scale = simplify $ (f - g * h)
--         (a_, b_, gcd) = extendedGcd g h
--         castCoeffs x = (fromIntegral x) :: PrimeField (p^(k+1))
--         f = fmap ( castCoeffs ) f_
--         g = fmap ( castCoeffs . PrimeField.toInteger ) g_
--         h = fmap ( castCoeffs . PrimeField.toInteger ) h_

hasMultipleRoots :: KnownNat p => Polynomial (PrimeField p) -> Bool
hasMultipleRoots p = (/=) (fromRing 1) (simplify $ gcd_ p (differentiate p))

factorInField :: Natural -> Polynomial Integer -> [ Polynomial Integer ]
factorInField n p = funcInField n p (fmap (fmap PrimeField.toInteger) . factor)

funcInField :: Natural -> Polynomial Integer -> (forall (p :: Nat). KnownNat p => Polynomial (PrimeField p) -> r) -> r
funcInField n poly func = 
    reifyNat (fromIntegral n)
    $ \(_ :: Proxy a) -> func $ fmap (\i -> fromInteger i :: PrimeField a) poly