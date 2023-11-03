{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE DataKinds, AllowAmbiguousTypes, ScopedTypeVariables, TypeFamilies #-}
module Polynomial.Hensel () where

import Polynomial.Ring
import Polynomial.Polynomial
import Polynomial.Squarefree
import Polynomial.Berlekamp()

import Data.Proxy
import GHC.TypeNats
import Data.Reflection
import Data.List qualified as List
import qualified Data.Ratio as Ratio
import Combinatorics qualified as Combinatorics

import Debug.Trace

{- OLD


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
{-
lift :: forall (p :: Nat) (k :: Nat). (KnownNat p, KnownNat k)
    => Polynomial Integer
    -> Integer
    -> Integer
lift f a = fromIntegral $ a + t * (p^k)
    where
        p :: Integer
        p = fromIntegral $ natVal (Proxy :: Proxy p)
        k :: Integer
        k = fromIntegral $ natVal (Proxy :: Proxy k)
        
        dfa = fromIntegral (evaluate a $ differentiate f) :: PrimeField p
        _fa_pm = fromIntegral (- (evaluate a f) // (p^k)) :: PrimeField p

        t = PrimeField.toInteger $ _fa_pm // dfa
-}


-- https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Yiduan.pdf
-- https://www.cmi.ac.in/~ramprasad/lecturenotes/comp_numb_theory/lecture26.pdf

{-
liftN :: forall (p :: Nat) (k :: Nat) . (KnownNat p, KnownNat k,  KnownNat (p^k))
    => Polynomial Integer 
    -> [Polynomial (PrimeField (p^k))]
liftN poly = (\r -> (monomial 1 1) + (monomial (fromInteger (-r) :: PrimeField (p^k)) 1))
            <$> lift_ 
            <$> (funcInField (fmap PrimeField.toInteger . roots) p poly)
    where
        lift_ :: Integer -> Integer
        lift_ = foldl (.) id ((\k_ -> reifyNat (fromIntegral k_) (\(_ :: Proxy k_) -> lift @p @k_ poly )) <$> (List.reverse [1..(k - 1)]))
        k = natVal $ (Proxy :: Proxy k)
        p = natVal $ (Proxy :: Proxy p)
-}

{-
-- find linear factors p (mod 13), then lift to factors to (mod 13^6), then recombine
factorize_linear :: Polynomial Integer -> [Polynomial Integer]
factorize_linear p = recombine p $ liftN @13 @6 p
-}


END OLD -}





{-

https://en.wikipedia.org/wiki/Hensel%27s_lemma#Linear_lifting

f === gh    mod p^k

take 
    D : D === f - gh    mod p^(k+1)

    c : aD === _ * h + c    mod p^(k+1)
    d : bD === _ * g + d    mod p^(k+1)

    g' = g + c
    h' = h + d

-}
liftPair_ :: forall (pk1 :: Nat). KnownNat pk1
    => Polynomial Integer
    -> Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
liftPair_ f lu (a,b) (g,h) = 
    ( expand $ fmap toIntegerNormal $ (toRing g) + beta*d
    , expand $ fmap injectInteger $ (toRing h) + beta*c
    )
    where
        -- beta = ( 1 - gamma ) // alpha
        betainv = fromInteger @(FiniteCyclicRing pk1) (leadingCoeff lu)
        beta = monomial (1 // betainv) 0

        delta = toInteger $ toRing $ f - lu * g * h

        c = toRing $ rem (a * delta) h
        d = toRing $ rem (b * delta) g

        toInteger = fmap toIntegerNormal . expand 
        toRing = fmap $ fromInteger @(FiniteCyclicRing pk1)
        rem x y = expand . snd $ polyDivMod x y

liftPair :: (Natural, Natural)
    -> Polynomial Integer
    -> Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
liftPair (p,k) f lf (g,h) = 
    reifyPrime (fromIntegral p)
        $ \(_ :: Proxy p) -> reifyNat ( fromIntegral (p^(k+1)) )
        $ \(_ :: Proxy pk1) -> 
            let 
                (r, a, b) = extendedGcd @(Polynomial (PrimeField p)) (fromInteger <$> g) (fromInteger <$> h)
            in
                liftPair_ @pk1 f lf (toIntegerNormal' <$> a // r, toIntegerNormal' <$> b // r) (g,h)


liftResidueFactors :: forall (n :: Nat) (k :: Nat) (p :: Prime n). (KnownPrime p, KnownNat k, KnownNat (Pow p k))
    => Polynomial Integer
    -> (Polynomial Integer, [ Polynomial Integer ])
    -> (Polynomial Integer, [ Polynomial (FiniteCyclicRing (Pow p k)) ])
liftResidueFactors poly (lu, basefact) = (,) lu $ (fmap fromInteger . snd . liftSequence) <$> (split [] basefact)
    where
        liftSequence :: (Polynomial Integer, Polynomial Integer) -> (Polynomial Integer, Polynomial Integer)
        liftSequence = foldl (flip (.)) id ( fmap ( \k_ -> liftPair (p, k_) poly lu ) [1..(k - 1)] )
        
        split :: Ring r => [(Polynomial r)] -> [(Polynomial r)] -> [(Polynomial r, Polynomial r)]
        split prev (h:t) = (expand $ foldr (*) 1 (prev ++ t), h) : (split (h:prev) t)
        split _ [] = []
        
        k = natVal $ (Proxy :: Proxy k)
        p = primeVal $ (Proxy :: Proxy p)

-- cast ( PrimeField p ) -> [ -p/2, p )
toIntegerNormal :: forall (n :: Nat). KnownNat n => FiniteCyclicRing n -> Integer
toIntegerNormal c_ = if c < ( p `div` 2) then c else c - p
    where
        c = (injectInteger c_) `mod` p
        p = fromIntegral $ natVal (Proxy :: Proxy n)

toIntegerNormal' :: forall (n :: Nat) (p :: Prime n). KnownPrime p => PrimeField p -> Integer
toIntegerNormal' c = toIntegerNormal $ toFiniteCyclicRing @n c

-- The-art-of-computer-programming.-Vol.2.-Seminumerical-algorithms-by-Knuth-Donald PAGE 452 F2
recombineResidueFactors :: forall (m :: Nat). KnownNat m 
    => Polynomial Integer 
    -> (Polynomial Integer, [Polynomial (FiniteCyclicRing m)])
    -> [Polynomial Integer]
recombineResidueFactors f (lu, lst) = List.nub $ recombine 1 f lst
    where
        recombine :: Integer -> Polynomial Integer -> [Polynomial (FiniteCyclicRing m)] -> [Polynomial Integer]
        recombine num u possibles
                | num > r = [] 
                | otherwise = (fmap (snd . primitivePart) factors) ++ recombine (num + 1) u remaining
            where
                remaining = possibles List.\\ (List.concat used)

                (used, factors) = unzip
                    $ List.filter ( divides (lu * u) . snd )
                    $ vbars

                -- vbars = [( polys used, their recombination )]
                vbars = fmap 
                        (\polys -> 
                            ( polys
                            , fmap toIntegerNormal
                                $ expand
                                $ (*) (fmap fromInteger lu)
                                $ foldr1 (*) polys
                            )
                        )
                        choices
                
                choices = Combinatorics.tuples (fromInteger num) possibles

                r :: Integer
                r = fromIntegral $ List.length possibles

                divides a b = (0 ==) . snd $ polyDivMod a b


factorInResidue :: Integer -> Polynomial Integer -> (Polynomial Integer, [ Polynomial Integer ])
factorInResidue n p = (,) (fromInteger lc) $ funcInField ((fmap (fmap toIntegerNormal' . snd . coercemonic . expand)) . snd . factor_squarefree . (// (fromInteger lc))) n p
    where
        lc = leadingCoeff p

funcInField :: (forall (n :: Nat) (p :: Prime n). KnownPrime p => Polynomial (PrimeField p) -> r) -> Integer -> Polynomial Integer -> r
funcInField func n poly = reifyPrime n $ (\(_ :: Proxy p) -> ( func $ fmap (fromInteger @(PrimeField p)) poly ))

factorsFromResidue :: Polynomial Integer -> Natural -> [Polynomial Integer]
factorsFromResidue poly m
    | irreducible n = reifyNat n
        $ \(_ :: Proxy p) -> reifyNat expo
        $ \(_ :: Proxy e) -> 
            fmap (expand . snd . coercemonic)
            $ recombineResidueFactors poly 
            $ liftResidueFactors @p @e poly 
            $ factorInResidue n poly -- calls berlekamp
    | otherwise = []
    where
        n = fromIntegral m
        expo = List.head [ e | e <- [1..], n ^ e >= bound ] -- mignotte's bound
        bound = ( sum $ fmap abs coeffs ) * ( 2 ^ (fromIntegral $ degree poly) )
        coeffs = fmap fst (toList poly)

stripFactors :: Polynomial Integer -> [Polynomial Integer] -> ( Polynomial Integer , [Polynomial Integer] )
stripFactors poly_ facts_ = 
        ( foldr (gcd_) poly $ fmap (removeFactor poly) facts
        , List.filter (divides poly) (facts)
        )
    where
        removeFactor p fact
            | p == 0 = p
            | divides p fact = removeFactor (divide p fact) fact
            | otherwise = p
        
        facts = fmap expand facts_
        poly = expand poly_

        divides a b = (0 ==) . snd $ polyDivMod a b

factorPrimitivePart :: Natural 
    -> Polynomial Integer 
    -> (Polynomial Integer, [Polynomial Integer])
factorPrimitivePart n p 
    | isUnit p = (p, [])
    | irreducible p = (1, [p])
    | otherwise = 
        map2 (facts ++) (factorPrimitivePart (n+1) poly)
    where
        (poly, facts) = stripFactors p (factorsFromResidue p n)
        map2 f (a,b) = (a, f b)


instance UFD (Polynomial Integer) where
    factor_squarefree :: Polynomial Integer -> (Polynomial Integer, [Polynomial Integer])
    factor_squarefree p_ = (expand $ (monomial u 0) * u2, lst)
        where
            (u2, lst) = factorPrimitivePart (fromIntegral $ head 
                [ p | p <- [ 5.. ]
                    , irreducible p
                    , all (/= 0) $ fmap (% p) coeffs
                ]) f
            coeffs = fst <$> toList f
            (u, f) = primitivePart p_

    squarefree :: Polynomial Integer -> Polynomial Integer
    squarefree = squarefree_field

    irreducible :: Polynomial Integer -> Bool
    irreducible p_
        | p /= p_ = False
        | (degree p == 0) && (not $ isUnit p) = True
        | otherwise = any isIrreducibleMod 
            [ prime | prime <- [(max 3 (deg + 1))..(max 3 $ (*) (2 ^ deg) $ sum $ map abs coeffs)] -- the range to search
                , irreducible prime -- prime is prime
                , all (/= 0) $ map (% prime) coeffs -- doesn't kill any coeffs
                ]
        where 
            isIrreducibleMod prime = funcInField irreducible prime p
            coeffs = filter (/= 0) $ fst <$> toList p
            deg = fromIntegral $ degree p
            p = expand $ squarefree p_


instance UFD (Polynomial Rational) where
    factor_squarefree :: Polynomial Rational -> (Polynomial Rational, [Polynomial Rational])
    factor_squarefree p =
        (\(u_, lst) -> (expand $ (monomial (1/u) 0) * (fromInteger <$> u_), snd . coercemonic . (fmap fromInteger) <$> lst))
        $ factor_squarefree @(Polynomial Integer)
        $ fmap Ratio.numerator
        $ expand 
        $ (*) p
        $ monomial u 0
        where
            u :: Rational
            u = fromInteger $ foldr1 lcm $ (Ratio.denominator . fst) <$> (toList p)
        
    squarefree = squarefree_field
    irreducible = \_ -> True

-- instance UFD (Polynomial Double) where
--     factor_squarefree = (\(u,lst) -> (fromRational <$> u, (fmap fromRational) <$> lst)) . factor_squarefree @(Polynomial Rational) . fmap toRational
--     squarefree = fmap fromRational . squarefree_field . fmap toRational