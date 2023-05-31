module Galois where

data Galois = GF (Integer, Integer) Integer

-- instance Eq Galois
--     (==) (GF (-1) i) (GF q i') = (i `mod` q) == (i' `mod` q)
--     (==) (GF q i) (GF _ i') = (i `mod` q) == (i' `mod` q)

-- instance Num Galois
--     (==) (GF (-1) i) (GF q i') = (i `mod` q) == (i' `mod` q)


-- mapGalois :: (Integer -> Integer -> Integer) -> Galois -> Galois -> Galois
-- mapGalois f (GF (-1) i) (GF q i') = GF q $ (f i i') `mod` q
-- mapGalois f (GF q i) (GF _ i') = GF q $ (f i i') `mod` q

-- gcdGalois :: Galois -> Galois -> Galois
-- gcdGalois (GF q i) (GF _ i')
--     | (i' `mod` q) == 0 = (GF q i)
--     | isZero (f // ng) = 1
--     | otherwise = gcdGalois ng (f % ng)



inverse :: Integer -> Integer -> Integer
inverse q e
  | e `mod` q == 0    = error "Zero does not have a multiplicative inverse"
  | otherwise = mod (snd (extendedEuclidean e q)) q


totient :: Integer -> Integer -> Integer
totient prime power = (prime ^ power) - (prime ^ (power - 1))


-- class Galois where
--     recip :: a -> a
--     recip (GF (p, e) i) = (i ^ ((totient p e) - 1)) `mod` (p ^ e)
--     fromRational :: Rational -> Galois
--     fromRational im