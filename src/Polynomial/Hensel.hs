{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE DataKinds, AllowAmbiguousTypes, ScopedTypeVariables, TypeFamilies #-}
module Polynomial.Hensel () where

import Polynomial.Ring
import Polynomial.Polynomial
import Polynomial.Squarefree
import Polynomial.Berlekamp()

import Data.Proxy
import Data.FiniteField.PrimeField qualified as PrimeField
import GHC.TypeNats
import Data.Reflection
import Data.List qualified as List
import qualified Data.Ratio as Ratio
import Combinatorics qualified as Combinatorics

-- x,y returns (c,a,b) such that ax + by = c = gcd(x,y)
extendedGcd :: ED r => r -> r -> (r, r, r)
extendedGcd a b | b == 0    = (a, 1, 0)
                | otherwise = 
                    let (q, r) = div_ a b
                        (d, x, y) = extendedGcd b r
                    in (d, y, x - q * y)

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
lift2 :: forall (pk1 :: Nat). KnownNat pk1
    => Polynomial Integer
    -> Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
lift2 f lu (a,b) (g,h) = ( expand $ toIntegerNormal <$> (fromInteger <$> g) + beta*d, expand $ PrimeField.toInteger <$> (fromInteger <$> h) + beta*c )
    where
        -- beta = ( 1 - gamma ) // alpha
        beta :: Polynomial (FiniteCyclicRing pk1)
        beta =  monomial (1 // (fromInteger $ leadingCoeff lu)) 0

        delta :: Polynomial (FiniteCyclicRing pk1)
        delta = expand $ fromInteger <$> f - lu * g * h

        c :: Polynomial (FiniteCyclicRing pk1)
        c = (<$>) fromInteger . expand . snd $ polyDivMod (a * (toIntegerNormal <$> delta)) h

        d :: Polynomial (FiniteCyclicRing pk1)
        d = (<$>) fromInteger . expand . snd $ polyDivMod (b * (toIntegerNormal <$> delta)) g


do_lift2 :: (Natural, Natural)
    -> Polynomial Integer
    -> Polynomial Integer
    -> (Polynomial Integer, Polynomial Integer)
    -> (Polynomial Integer, Polynomial Integer)
do_lift2 (p,k) f lf (g,h) = 
    reifyPrime (fromIntegral p)
        (  \(_ :: Proxy p) -> 
            let (r, a, b) = extendedGcd @(Polynomial (PrimeField p)) (fromInteger <$> g) (fromInteger <$> h)
            in reifyNat 
                ( fromIntegral (p^(k+1)) )
                ( \(_ :: Proxy pk1) -> 
                    lift2 @pk1 f lf (toIntegerNormal' <$> a // r, toIntegerNormal' <$> b // r) (g,h) 
                )
        )


lift_to :: forall (n :: Nat) (k :: Nat) (p :: Prime n). (KnownPrime p, KnownNat k, KnownNat (Pow p k))
    => Polynomial Integer
    -> (Polynomial Integer, [Polynomial (FiniteCyclicRing (Pow p k))])
lift_to poly = (,) lu $ (fmap fromInteger . snd . lift_) <$> (split [] basefact)
    where
        (lu, basefact) = factorInField p poly

        lift_ :: (Polynomial Integer, Polynomial Integer) -> (Polynomial Integer, Polynomial Integer)
        lift_ = foldr (.) id ((\k_ -> do_lift2 (p, k_) poly lu ) <$> (List.reverse [1..(k - 1)]))
        
        split :: Ring r => [(Polynomial r)] -> [(Polynomial r)] -> [(Polynomial r, Polynomial r)]
        split prev (h:t) = (expand $ foldr (*) 1 (prev ++ t), h) : (split (h:prev) t)
        split _ [] = []
        
        k = natVal $ (Proxy :: Proxy k)
        p = primeVal $ (Proxy :: Proxy p)


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

-- cast ( PrimeField p ) -> [ -p/2, p )
toIntegerNormal :: forall (n :: Nat). KnownNat n => FiniteCyclicRing n -> Integer
toIntegerNormal c_ = if c < ( p `div` 2) then c else c - p
    where
        c = (PrimeField.toInteger c_) `mod` p
        p = fromIntegral $ natVal (Proxy :: Proxy n)

toIntegerNormal' :: forall (n :: Nat) (p :: Prime n). KnownPrime p => PrimeField p -> Integer
toIntegerNormal' c_ = if c < ( p `div` 2) then c else c - p
    where
        c = (PrimeField.toInteger $ toFiniteCyclicRing c_) `mod` p
        p = fromIntegral $ primeVal (Proxy :: Proxy p)

-- The-art-of-computer-programming.-Vol.2.-Seminumerical-algorithms-by-Knuth-Donald PAGE 452 F2
recombine :: forall (m :: Nat). KnownNat m 
    => Polynomial Integer 
    -> (Polynomial Integer, [Polynomial (FiniteCyclicRing m)])
    -> [Polynomial Integer]
recombine f (lu, lst) = List.nub $ recombine_ 1 f lst
    where
        recombine_ :: Integer -> Polynomial Integer -> [Polynomial (FiniteCyclicRing m)] -> [Polynomial Integer]
        recombine_ d u polys = if d > r then [] else ((snd . primitivePart) <$> out) ++ recombine_ (d + 1) u remaining
            where
                remaining = polys List.\\ (List.concat remove)
                (remove, out) = unzip $ List.filter ( \(_, p) -> (==) 0 . snd $ polyDivMod (lu * u) p ) vbars
                vbars = (\lst_ -> (lst_, fmap toIntegerNormal $ expand $ (*) (fromInteger <$> lu) $ foldr1 (*) lst_)) <$> choices
                choices = Combinatorics.tuples (fromInteger d) polys
                r :: Integer
                r = fromIntegral $ List.length polys
                -- m :: Integer
                -- m = fromIntegral $ natVal (Proxy :: Proxy m)
                



-- hasMultipleRoots :: ED r => Polynomial r -> Bool
-- hasMultipleRoots p = (/=) (1) (expand $ gcd_ p (differentiate p))

factorInField :: Natural -> Polynomial Integer -> (Polynomial Integer, [ Polynomial Integer ])
factorInField n p = (,) (fromInteger lc) $ funcInField ((fmap (fmap toIntegerNormal' . snd . coercemonic . expand)) . snd . factor_squarefree . (// (fromInteger lc))) n p
    where
        lc = leadingCoeff p

funcInField :: (forall (n :: Nat) (p :: Prime n). KnownPrime p => Polynomial (PrimeField p) -> r) -> Natural -> Polynomial Integer -> r
funcInField func n poly = 
    reifyPrime (fromIntegral n) $ (\(_ :: Proxy p) -> ( func $ fmap (fromInteger @(PrimeField p)) poly ))

factors_from_base_prime :: Polynomial Integer -> Natural -> [Polynomial Integer]
factors_from_base_prime poly m  | irreducible n = reifyNat n $ \(_ :: Proxy p) -> recombine poly $ lift_to @p @5 poly
                                | otherwise = []
                                where n = fromIntegral m

factor_primitive_part :: Natural -> Polynomial Integer -> (Polynomial Integer, [Polynomial Integer])
factor_primitive_part n p | isUnit p = (p, [])
                    | irreducible p = (1, [p])
                    | otherwise =
                        ( \(poly, facts) -> append_factors facts $ factor_primitive_part (n+1) poly )
                        $ foldr (\fact (poly, rest) -> append_factors rest (remove_powers poly fact)) (p, []) factors
                    where
                        remove_powers :: Polynomial Integer -> Polynomial Integer -> (Polynomial Integer, [Polynomial Integer])
                        remove_powers base fact | ((==) 0 . snd $ polyDivMod base fact) = (fst $ remove_powers (base /. fact) fact, [fact])
                                                | otherwise = (base, [])

                        append_factors :: [a] -> (a, [a]) -> (a,[a])
                        append_factors l1 (a,l2) = (a, l1 ++ l2)

                        factors = factors_from_base_prime p n


instance UFD (Polynomial Integer) where
    -- factor p (mod 13), then lift to factors to (mod 13^6), then recombine
    factor_squarefree :: Polynomial Integer -> (Polynomial Integer, [Polynomial Integer])
    factor_squarefree p_ = (expand $ (monomial u 0) * u2, lst)
        where
            (u2, lst) = factor_primitive_part 7 p
            (u, p) = primitivePart p_

    squarefree :: Polynomial Integer -> Polynomial Integer
    squarefree = squarefree_field

    irreducible :: Polynomial Integer -> Bool
    irreducible p
        | squarefree p /= p = False
        | otherwise = ( (degree p == 0) && (not $ isUnit p) ) || ( isIrreducibleMod prime1 )
        where 
            isIrreducibleMod primen = reifyPrime primen ( \(_ :: Proxy prime) -> foldr (&&) True $ fmap (\a -> (a == 1) || (a == p) ) $ fmap (gcd_ p) $ (\_ -> []) $ error . show $ fmap (fmap toIntegerNormal') $ snd $ factor_squarefree $ squarefree $ fromInteger @(PrimeField prime) <$> (squarefree p) )
            prime1 = ( List.head [ p_ | p_ <- [(deg + 1)..], (lc `mod` p_) /= 0, irreducible p_ ] )

            deg = degree p
            lc = leadingCoeff p


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
    irreducible = undefined

-- instance UFD (Polynomial Double) where
--     factor_squarefree = (\(u,lst) -> (fromRational <$> u, (fmap fromRational) <$> lst)) . factor_squarefree @(Polynomial Rational) . fmap toRational
--     squarefree = fmap fromRational . squarefree_field . fmap toRational