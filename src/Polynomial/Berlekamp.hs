-- {-# LANGUAGE TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
module Polynomial.Berlekamp (berlekamp) where

import Polynomial.Squarefree
import Polynomial.Polynomial
import Polynomial.Ring
import Polynomial.CustomMatrix

import Data.Matrix (Matrix, fromLists, toLists, identity, rref, (<|>))
import Data.Either.Combinators qualified as Either
import Data.List qualified as List
import Data.FiniteField.PrimeField qualified as PrimeField
import GHC.TypeNats
import Data.Proxy

fill :: KnownPrime p => Integer -> Integer -> Polynomial (PrimeField p) -> Matrix (PrimeField p)
fill q n p = fromLists $ fmap ( \i -> torowvector (n - 1) $ (monomial 1 $ i * q) % p ) [1..(fromIntegral n)]
  where
    torowvector n_ p_ = fmap (flip coeff p_) [0..n_]

unfill :: Ring r => [[r]] -> [Polynomial r]
unfill = 
  fmap ( \lst ->
    expand
    $ foldr (+) 0
    $ zipWith monomial lst [0 ..]
  )

formmatrix :: forall p. KnownPrime p => Polynomial (PrimeField p) -> Matrix (PrimeField p)
formmatrix p_ = form (primeVal (Proxy :: Proxy p)) (degree p_) p_
  where
    form q n p = (fill (fromIntegral q) n p - identity (fromIntegral n)) 
      <|> identity (fromIntegral n)

-- DATA.MATRIX CAN'T REDUCE SOME NON-INVERTABLE MATRICES. >:(
nullspaceBasis :: KnownPrime p => Matrix (PrimeField p) -> [ Polynomial (PrimeField p) ]
nullspaceBasis m = 
  unfill
  $ fmap (\lst -> drop (length lst `div` 2 ) lst)
  -- $ (Either.fromRight $ error "i think the rref function sucks at its job")
  $ (Either.fromRight $ gaussianJordanElimination $ toLists m)
  $ fmap toLists
  $ rref m


berlekampGcds :: forall p. KnownPrime p => Polynomial (PrimeField p) -> Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
berlekampGcds f g = fmap ( \i -> ( gcd_ f (g - (fromIntegral i)) ) ) [0..(fromIntegral $ primeVal (Proxy :: Proxy p) :: Integer)]

removeReducible :: KnownPrime p => [ Polynomial (PrimeField p) ] -> [ Polynomial (PrimeField p) ]
removeReducible = removeReducible_ []
  where
    removeReducible_ prev (h:t) = removeReducible_ ((reduce (prev ++ t) h) : prev) t
    removeReducible_ out [] = out

    reduce :: KnownPrime p => [ Polynomial (PrimeField p) ] -> Polynomial (PrimeField p) -> Polynomial (PrimeField p)
    reduce [] p = p
    reduce (h:t) p  | (h == p) = reduce t p
                    | (isZero $ p % h) && (not . isUnit $ h // p) = reduce (h:t) (p // h)
                    | otherwise = reduce t p

-- removeReducible lst = List.filter ( \p -> (==) Nothing $ List.find (\p2 -> (p2 /= p) && (isZero $ p % p2) && (not . isUnit $ p2 // p)) lst ) lst

findPartners :: KnownPrime p => Polynomial (PrimeField p) -> Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
findPartners p f = (:) f $ fmap (\n -> p // (f ^ n)) [1..(degree p - degree f)]

possibleFactors :: KnownPrime p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
possibleFactors p =
  List.filter (\p_ -> not $ isUnit p_ || isZero p_)
  $ List.nub
  $ fmap expand
  $ List.filter (isZero . (%) p)
  $ List.nub
  $ List.concatMap (findPartners p)
  $ List.nub
  $ List.concatMap (berlekampGcds p)
  -- $ fmap coerceMonic
  $ nullspaceBasis 
  $ formmatrix p

-- sqfrFactors :: Prime p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
-- sqfrFactors p = 
--   fmap expand
--   $ (:) p
--   $ List.filter ((/=) 1)
--   $ List.nub
--   $ fmap (expand . gcd_ p)
--   $ possibleFactors p

berlekamp :: KnownPrime p => Polynomial (PrimeField p) -> (Polynomial (PrimeField p), [ Polynomial (PrimeField p) ])
berlekamp p = 
  (,) lc
  $ List.nub
  $ (fmap $ expand . snd . coercemonic)
  $ removeReducible
  $ List.nub
  $ (fmap $ expand . snd . purePart)
  $ possibleFactors (p // lc)
  where
    lc = (monomial (leadingCoeff p) 0)

instance (KnownPrime p) => UFD (Polynomial (PrimeField p)) where
  factor_squarefree = berlekamp
  squarefree = squarefree_field