import Data.Matrix (Matrix, fromLists, toLists, identity, rref, (<|>), splitBlocks)
import qualified Data.Ratio as Ratio
import qualified Data.Either.Combinators as Either
import Squarefree
import GHC.Base (Double)
import Polynomial
import qualified Data.List as List


xnmodf :: Ring r => Deg -> Polynomial r -> Polynomial r
xnmodf n f = Monomial 1 n % f

tovec :: Ring r => Deg -> Polynomial r -> [r]
tovec n p = fmap (coeff $ p) [0..n]

fill :: Ring r => Deg -> Deg -> Polynomial r -> Matrix r
fill q n p = fromLists
  $ fmap 
    ( \i -> tovec (n - 1) $ xnmodf (i * q) p )
    [1..(fromIntegral n)]

form :: Ring r => Deg -> Deg -> Polynomial r -> Matrix r
form q n p = (fill q n p - identity (fromIntegral n))
  <|> identity (fromIntegral n)

formauto :: Ring r => Polynomial r -> Matrix r
formauto p = form 1 (degree p) p

unfill :: Ring r => [[r]] -> [Polynomial r]
unfill = 
  fmap ( \lst ->
    simplify
    $ foldr (+) 0
    $ zipWith Monomial lst [0 ..]
  )

nullspace :: (Fractional r, Ring r) => Polynomial r -> [ Polynomial r ]
nullspace p = 
  Either.fromRight []
  $ Either.mapRight unfill 
  $ Either.mapRight (fmap (\lst -> drop (length lst `div` 2 ) lst))
  $ Either.mapRight toLists
  $ rref 
  $ formauto p


possibleFactors :: (Fractional r, Ring r) => Polynomial r -> [ Polynomial r ]
possibleFactors p =
  fmap (simplify . foldr (+) 0) . filter ((<)0.length)
  $ List.subsequences
  -- $ List.filter (\x -> degree (simplify $ p % x) == 0)
  $ nullspace p

sqfrFactors :: (Fractional r, Ring r) => Polynomial r -> [ Polynomial r ]
sqfrFactors p = 
  fmap simplify
  $ (:) p
  $ List.filter ((/=) 1)
  $ List.nub
  $ fmap (simplify . gcd_ p)
  $ possibleFactors p

factors :: (Fractional r, Ring r) => Polynomial r -> [ Polynomial r ]
factors p = 
  List.filter (\q -> (simplify $ p % q) == 0)
  $ (\lst ->
    List.filter
    ( \e ->
      not
      $ List.elem e
      $ fmap (simplify . foldr (*) 1) . filter ((<)1.length)
      $ List.subsequences
      $ lst
    )
    lst
  )
  $ sqfrFactors
  $ simplify
  $ squareFree p