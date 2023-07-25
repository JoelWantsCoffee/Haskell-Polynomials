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
extendedGcd a b | isZero b  = (a, 1, 0)
                | otherwise = 
                    let (q, r) = div_ a b
                        (d, x, y) = extendedGcd b r
                    in (d, y, x - (q // y))


extGcd :: Ring r => r -> r -> (r,r,r)
extGcd a b = extGcd_ (a,1,0) (b,0,1)

extGcd_ :: Ring r => (r,r,r) -> (r,r,r) -> (r,r,r)
extGcd_ (r0, s0, t0) (r1, s1, t1)
    | isZero r1 = (r0, s0, t0)
    | otherwise = extGcd_ (r1, s1, t1) (r0 - q*r1, s0 - q*s1, t0 - q*t1)
    where
        q = r0 // r1

bezoutGcd :: Ring r => r -> r -> (r,r,r)
bezoutGcd a b = 
    if isZero a then 
        (b, 0, 1)
    else
        let 
            (q, r) = div_ b a
            (d, s, t) = bezoutGcd r (a % b)
        in 
            (d, t - q * s, s)


{-

f === gh    mod p^k

take 
    D : D === f - gh    mod p^(k+1)

    c : aD === _ * h + c    mod p^(k+1)
    d : bD === _ * g + d    mod p^(k+1)

    g' = g + c
    h' = h + d

-}
lift2 :: forall (pk1 :: Nat). KnownNat pk1
    => Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
lift2 f (a,b) (g,h) = ( PrimeField.toInteger <$> (fromInteger <$> g) + d, PrimeField.toInteger <$> (fromInteger <$> h) + c)
    where
        delta :: Polynomial (PrimeField pk1)
        delta = simplify $ fromInteger <$> f - g * h

        c :: Polynomial (PrimeField pk1)
        c = fromInteger <$> (a * (PrimeField.toInteger <$> delta)) % h

        d :: Polynomial (PrimeField pk1)
        d = fromInteger <$> (b * (PrimeField.toInteger <$> delta)) % g


do_lift2 :: (Natural, Natural)
    -> Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
do_lift2 (p,k) f (g,h) = 
    reifyNat (fromIntegral p) ( 
        \(_ :: Proxy p) -> 
            let (r,a,b) = extendedGcd @(Polynomial (PrimeField p)) (fromInteger <$> g) (fromInteger <$> h)
            in reifyNat (fromIntegral (p^(k+1))) ( \(_ :: Proxy pk1) -> lift2 @pk1 f (PrimeField.toInteger <$> a // r, PrimeField.toInteger <$> b // r) (g,h) )
    )


        

liftN2 :: forall (p :: Nat) (k :: Nat) . (KnownNat p, KnownNat k,  KnownNat (p^k))
    => Polynomial Integer 
    -> [Polynomial (PrimeField (p^k))]
liftN2 poly = (fmap fromInteger . fst . lift_) <$> (break [] $ factorInField p poly)
    where
        lift_ :: (Polynomial Integer, Polynomial Integer) -> (Polynomial Integer, Polynomial Integer)
        lift_ = foldl (.) id ((\k_ -> do_lift2 (natVal (Proxy :: Proxy p), k_) poly ) <$> (List.reverse [1..(k - 1)]))
        
        break :: Ring r => [(Polynomial r)] -> [(Polynomial r)] -> [(Polynomial r, Polynomial r)]
        break prev (h:t) = (h, simplify $ foldr (*) 1 (prev ++ t)) : (break (h:prev) t)
        break _ [] = []
        
        k = natVal $ (Proxy :: Proxy k)
        p = natVal $ (Proxy :: Proxy p)


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


-- https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Yiduan.pdf
-- https://www.cmi.ac.in/~ramprasad/lecturenotes/comp_numb_theory/lecture26.pdf


liftN :: forall (p :: Nat) (k :: Nat) . (KnownNat p, KnownNat k,  KnownNat (p^k)) 
    => Polynomial Integer 
    -> [Polynomial (PrimeField (p^k))]
liftN poly = (\r -> x + (fromRing $ ( fromInteger (-r) :: PrimeField (p^k) )))
            <$> lift_ 
            <$> (funcInField (fmap PrimeField.toInteger . roots) p poly)
    where
        lift_ :: Integer -> Integer
        lift_ = foldl (.) id ((\k_ -> reifyNat (fromIntegral k_) (\(_ :: Proxy k_) -> lift @p @k_ poly )) <$> (List.reverse [1..(k - 1)]))
        k = natVal $ (Proxy :: Proxy k)
        p = natVal $ (Proxy :: Proxy p)


factorize_linear :: Polynomial Integer -> [Polynomial Integer]
factorize_linear p = recombine p $ liftN @13 @6 p

factorize_nonlinear :: Polynomial Integer -> [Polynomial Integer]
factorize_nonlinear p = recombine p $ simplify <$> liftN2 @13 @6 p

-- The-art-of-computer-programming.-Vol.2.-Seminumerical-algorithms-by-Knuth-Donald PAGE 452 F2
recombine :: KnownNat m => Polynomial Integer -> [Polynomial (PrimeField m)] -> [Polynomial Integer]
recombine f lst = recombine_ 1 f lst

recombine_ :: forall (m :: Nat). KnownNat m 
    => Integer 
    -> Polynomial Integer 
    -> [Polynomial (PrimeField m)] 
    -> [Polynomial Integer]
recombine_ d poly polys =
        if d > r
        then []
        else (++) out 
            $ recombine_ (d + 1) poly remaining
    where
        remaining = polys List.\\ (List.concat remove)
        (remove, out) = unzip $ List.filter ( \(_, p) -> isZero $ (poly % p) ) vbars
        vbars = (\lst -> (lst, fmap (normalise . PrimeField.toInteger) $ simplify $ foldr1 (*) lst)) <$> choices
        choices = Combinatorics.tuples (fromInteger d) polys
        m = fromIntegral $ natVal (Proxy :: Proxy m)
        r = fromIntegral $ List.length polys
        normalise = \c -> if c < (m `div` 2) then c else c - m


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
factorInField = funcInField (fmap (fmap PrimeField.toInteger . simplify) . factor)

funcInField :: (forall (p :: Nat). KnownNat p => Polynomial (PrimeField p) -> r) -> Natural -> Polynomial Integer  -> r
funcInField func n poly = 
    reifyNat (fromIntegral n)
    $ \(_ :: Proxy a) -> func $ fmap (\i -> fromInteger i :: PrimeField a) poly