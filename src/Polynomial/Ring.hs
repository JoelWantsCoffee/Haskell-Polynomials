{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}

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
    , Natural
    -- , MonoidRing(..)
    , injectInteger
    , reifyPrime
    , primeVal
    , toFiniteCyclicRing
    , extendedGcd
    ) where

import qualified Data.Mod as M
import GHC.TypeNats
import Data.Reflection
import Data.Proxy

newtype Superclass a = Superclass a

instance Eq a => Eq (Superclass a) where
    (==) (Superclass a) (Superclass b) = a == b

instance Num a => Num (Superclass a) where
    (+) (Superclass a) (Superclass b) = Superclass $ a + b
    (*) (Superclass a) (Superclass b) = Superclass $ a * b
    abs (Superclass a) = Superclass $ abs a
    signum (Superclass a) = Superclass $ signum a
    fromInteger = Superclass . fromInteger
    negate (Superclass a) = Superclass $ negate a

instance (Ring a) => Ring (Superclass a) where
    isUnit (Superclass a) = isUnit a

instance Field a => ED (Superclass a) where
    (//) (Superclass a) (Superclass b) = Superclass $ a * (inv b)
    (%) _ _ = Superclass 0

instance Field a => UFD (Superclass a) where
    factor_squarefree a = (a, [])
    squarefree a = a
    irreducible _ = False

instance ED a => GCDD (Superclass a) where
    gcd_ (Superclass a) (Superclass b) = Superclass . (\(c, _, _) -> c) $ extendedGcd a b 

-- x,y returns (c,a,b) such that ax + by = c = gcd(x,y)
extendedGcd :: ED r => r -> r -> (r, r, r)
extendedGcd a b | b == 0    = (a, 1, 0)
                | otherwise = (d, y, x - q * y)
                where
                    (q, r) = div_ a b
                    (d, x, y) = extendedGcd b r

class (Num a, Eq a) => Ring a where
    isUnit :: a -> Bool
    tryInvert :: a -> a

class Ring a => GCDD a where
    gcd_ :: a -> a -> a

class Ring a => UFD a where
    factor_squarefree :: a -> (a, [a])
    squarefree :: a -> a
    irreducible :: a -> Bool

class Ring a => ED a where
    (//) :: a -> a -> a
    (%) :: a -> a -> a
    euclidean :: a -> Integer
    div_ :: a -> a -> (a,a)
    div_ a b = (a // b, a % b) 

class Ring a => Field a where
    inv :: a -> a

-- INTEGER 

instance Ring Integer where
    isUnit 1 = True
    isUnit (-1) = True
    isUnit _ = False
    tryInvert (-1) = -1
    tryInvert 1 = 1
    tryInvert _ = error "cannot invert"

instance GCDD Integer where
    gcd_ = gcd

instance UFD Integer where
    factor_squarefree = undefined
    squarefree = undefined
    irreducible i   | i == 0    = False
                    | isUnit i  = False
                    | i > 1     = null [ x | x <- [2 .. floor (sqrt (fromIntegral i :: Double))], i `mod` x == 0 ]
                    | otherwise = irreducible (-i)

instance ED Integer where
    (//) = div
    (%) = mod
    div_ = divMod
    euclidean = id

-- RATIONALS

instance Ring Rational where
    isUnit = (/=) 0
    tryInvert = (/) 1

instance Field Rational where
    inv = (/) 1

deriving via (Superclass Rational) instance ED Rational
deriving via (Superclass Rational) instance UFD Rational
deriving via (Superclass Rational) instance GCDD Rational

-- INTEGER QUOTIENT RINGS 

type FiniteCyclicRing (n :: Nat) = M.Mod n

instance KnownNat p => Ring (FiniteCyclicRing p) where
    isUnit = isJust . M.invertMod
        where
            isJust :: Maybe a -> Bool
            isJust (Just _) = True
            isJust Nothing  = False
    tryInvert a = case M.invertMod a of
        Just b -> b
        _ -> error "cannot invert."

injectInteger :: KnownNat n => FiniteCyclicRing n -> Integer
injectInteger = fromIntegral . M.unMod

-- PRIME STUFF

data Prime (n :: Nat)

type family AssumePrime (n :: Nat) :: Prime n

type family Pow (p :: Prime n) (k :: Nat) :: Nat where
    Pow (p :: Prime n) k = n ^ k

newtype PrimeField (p :: Prime n) = PrimeField (FiniteCyclicRing n)
    deriving (Eq, Ord, Num, Ring, Fractional, Bounded, Enum)

instance KnownPrime p => GCDD (PrimeField p) where
    gcd_ 0 b = b
    gcd_ a _ = a

instance KnownPrime p => ED (PrimeField p) where
    (//) = (/)
    (%) _ _ = 0

instance KnownPrime p => UFD (PrimeField p) where
    factor_squarefree a = (a, [])
    squarefree a = a
    irreducible _ = False

instance KnownPrime p => Show (PrimeField p) where
    show (PrimeField e) = show e

toFiniteCyclicRing :: forall (n :: Nat) (p :: Prime n). PrimeField p -> FiniteCyclicRing n
toFiniteCyclicRing (PrimeField n) = n

class KnownNat n => KnownPrime (p :: Prime n) where
    primeVal :: Proxy p -> Natural

instance KnownNat n => KnownPrime (p :: Prime n) where
    primeVal (_ :: Proxy p) = natVal $ Proxy @n

reifyPrime :: forall r. Integer -> (forall (n :: Nat) (p :: Prime n). KnownPrime p => Proxy p -> r) -> r
reifyPrime i f  
        | irreducible i = reifyNat i (f . assumePrime)
        | otherwise = error (show i ++ " is not prime.")

assumePrime :: forall (n :: Nat) (p :: Prime n) . (KnownNat n, KnownPrime p) => Proxy n -> Proxy p
assumePrime Proxy = Proxy

instance KnownPrime p => Field (PrimeField p) where
    inv = (/) 1

-- monoid rings

-- data MonoidRing m r where
--     Monomial :: r -> m -> MonoidRing m r
--     Sum :: MonoidRing m r -> MonoidRing m r -> MonoidRing m r
--     Product :: MonoidRing m r -> MonoidRing m r -> MonoidRing m r


-- instance Semigroup Natural where
--     (<>) = (+)

-- instance Monoid Natural where
--     mempty = 0

-- -- remove Product
-- ungroup :: (Monoid m, Ring r) => MonoidRing m r -> MonoidRing m r
-- ungroup (Monomial c d) = Monomial c d
-- ungroup (Sum f g) = Sum (ungroup f) (ungroup g)
-- ungroup (Product (Monomial c0 d0) (Monomial c1 d1)) = Monomial (c0 * c1) (d0 <> d1)
-- ungroup (Product (Sum f g) h) = Sum (ungroup $ Product f h) (ungroup $ Product g h)
-- ungroup (Product f (Sum g h)) = Sum (ungroup $ Product f g) (ungroup $ Product f h)
-- ungroup (Product f g) = ungroup $ Product (ungroup f) (ungroup g)

-- -- reduce to only Sum and Monomial constructors
-- setThemUp :: (Monoid m, Ring r) => MonoidRing m r -> MonoidRing m r
-- setThemUp (Monomial c d) = Monomial c d
-- setThemUp (Sum (Monomial c d) b) = Sum (Monomial c d) (setThemUp b)
-- setThemUp (Sum (Sum a b) c) = setThemUp $ Sum a (Sum b c)
-- setThemUp a = setThemUp $ ungroup a

-- -- sort Sum and Monomial constructors, returns a only-right-recursive tree
-- sortThemOut :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> MonoidRing m r
-- sortThemOut (Monomial c_ d) = Monomial c_ d
-- sortThemOut (Sum (Monomial c_ d_) t) = Sum big $ sortThemOut rest
--         where 
--             (big, rest) = findBig (Monomial c_ d_) t id
--             findBig :: (Ord m, Monoid m, Ring r)
--                 => MonoidRing m r 
--                 -> MonoidRing m r 
--                 -> (MonoidRing m r -> MonoidRing m r)
--                 -> (MonoidRing m r, MonoidRing m r)
--             findBig (Monomial maxc maxd) (Monomial c d) f
--                 | d > maxd  = (Monomial c d, f $ Monomial maxc maxd)
--                 | otherwise = (Monomial maxc maxd, f $ Monomial c d)
--             findBig (Monomial maxc maxd) (Sum (Monomial c d) next) f
--                 | d > maxd  = findBig (Monomial c d) next ((.) f $ Sum (Monomial maxc maxd))
--                 | otherwise = findBig (Monomial maxc maxd) next ((.) f $ Sum (Monomial c d))
--             findBig b n f = findBig b (setThemUp n) f
-- sortThemOut a = sortThemOut $ setThemUp a

-- -- remove duplicate power monomials
-- knockThemDown :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> MonoidRing m r
-- knockThemDown (Monomial c d) = Monomial c d
-- knockThemDown (Sum (Monomial 0 _) a) = knockThemDown a
-- knockThemDown (Sum a (Monomial 0 _)) = knockThemDown a
-- knockThemDown (Sum (Monomial c d) (Sum (Monomial c' d') t))
--     | d == d' = knockThemDown $ Sum (Monomial (c + c') d) t
--     | otherwise = Sum (Monomial c d) $ knockThemDown (Sum (Monomial c' d') t)
-- knockThemDown (Sum (Monomial c d) (Monomial c' d'))
--     | d == d' = Monomial (c + c') d
--     | otherwise = Sum (Monomial c d) (Monomial c' d')
-- knockThemDown a = knockThemDown $ sortThemOut a

-- -- convert to an only-right-recursive tree where each monomial degree appears at most once 
-- expand :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> MonoidRing m r
-- expand = knockThemDown . sortThemOut . setThemUp

-- instance (Ord m, Monoid m, Ring r) => Num (MonoidRing m r) where
--     (+) = Sum
--     (*) = Product
--     abs = id
--     signum _ = Monomial 1 mempty
--     negate = (*) (Monomial (-1) mempty)
--     fromInteger i = Monomial (fromInteger i) mempty

-- instance (Ord m, Monoid m, Ring r) => Ring (MonoidRing m r) where
--     isUnit p = isUnit_ $ expand p
--         where
--             isUnit_ (Monomial c mempty) = isUnit c
--             isUnit_ _ = False

-- instance (Ord m, Monoid m, Ring r) => Eq (MonoidRing m r) where
--     (==) x y = isZero (x - y)
--         where
--             isZero p = isZero_ $ expand p
--             isZero_ (Sum a b) = (isZero_ a) && (isZero_ b)
--             isZero_ (Monomial a _) = a == 0
--             isZero_ (Product a b) = (isZero_ a) || (isZero_ b)

-- degree :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> m
-- degree = degree_expanded_unsafe . expand
--     where
--         degree_expanded_unsafe :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> m
--         degree_expanded_unsafe (Monomial 0 _) = mempty
--         degree_expanded_unsafe (Monomial _ deg) = deg
--         degree_expanded_unsafe (Sum p1 p2) = max (degree p1) (degree p2)
--         degree_expanded_unsafe (Product p1 p2) = degree p1 <> degree p2

-- leadingCoeff :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> r
-- leadingCoeff = leadingCoeff_ . expand
--     where
--         leadingCoeff_ :: (Ord m, Monoid m, Ring r) => MonoidRing m r -> r
--         leadingCoeff_ (Monomial c _) = c 
--         leadingCoeff_ (Product a b) = error "what"
--         leadingCoeff_ (Sum a b) = leadingCoeff_ a