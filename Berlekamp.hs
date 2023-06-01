module Berlekamp where

import Squarefree
import Polynomial
import Ring

import Data.Matrix (Matrix, fromLists, toLists, identity, rref, (<|>), splitBlocks)
import qualified Data.Ratio as Ratio
import qualified Data.Either.Combinators as Either
import GHC.Base (Double)
import qualified Data.List as List
import Data.FiniteField.PrimeField
import GHC.TypeNats


xnmodf :: Ring r => Degree -> Polynomial r -> Polynomial r
xnmodf n f = (Monomial 1 n) % f

toRowVec :: Ring r => Integer -> Polynomial r -> [r]
toRowVec n p = fmap (coeff $ p) [0..n]

fill :: Ring r => Integer -> Integer -> Polynomial r -> Matrix r
fill q n p = fromLists
  $ fmap 
    ( \i -> toRowVec (n - 1) $ xnmodf (i * q) p )
    [1..(fromIntegral n)]

form :: Ring r => Integer -> Integer -> Polynomial r -> Matrix r
form q n p = (fill q n p - identity (fromIntegral n))
  <|> identity (fromIntegral n)

formauto :: KnownNat p => Polynomial (PrimeField p) -> Matrix (PrimeField p)
formauto p = form (fieldOrder p) (degree p) p

unfill :: Ring r => [[r]] -> [Polynomial r]
unfill = 
  fmap ( \lst ->
    simplify
    $ foldr (+) 0
    $ zipWith Monomial lst [0 ..]
  )

nullspaceBasis :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
nullspaceBasis p = 
  Either.fromRight []
  $ Either.mapRight unfill 
  $ Either.mapRight (fmap (\lst -> drop (length lst `div` 2 ) lst))
  $ Either.mapRight toLists
  $ rref 
  $ formauto p

berlekampGcds :: KnownNat p => Polynomial (PrimeField p) -> Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
berlekampGcds f g = fmap ( \i -> ( gcd_ f (g - (fromIntegral i)) ) ) [0..(fieldOrder f)]

removeReducible :: KnownNat p => [ Polynomial (PrimeField p) ] -> [ Polynomial (PrimeField p) ]
removeReducible lst = List.filter ( \p -> (==) Nothing $ List.find (\p2 -> (p2 /= p) && (isZero $ p % p2) && (not . isUnit $ p2 // p)) lst ) lst

possibleFactors :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
possibleFactors p =
  List.filter (not . isUnit)
  $ List.nub
  $ fmap simplify
  $ List.concatMap (berlekampGcds p)
  $ nullspaceBasis p


sqfrFactors :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
sqfrFactors p = 
  fmap simplify
  $ (:) p
  $ List.filter ((/=) 1)
  $ List.nub
  $ fmap (simplify . gcd_ p)
  $ possibleFactors p

factors :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
factors = 
  List.nub
  . (fmap simplify)
  . (fmap coerceMonic)
  . removeReducible
  . possibleFactors
  . squareFree

berlekamp :: KnownNat p => Polynomial (PrimeField p) -> [ Polynomial (PrimeField p) ]
berlekamp = factors