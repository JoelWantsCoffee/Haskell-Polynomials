module Main where

import System.Environment
import Polynomial.Factor
import Text.Read (readMaybe)
import Data.Proxy

instance Ring Double

data Token r = Coeff r | Var | Exp Integer | Plus deriving (Show, Eq)

-- The lexer function breaks the input string into Tokens.
lexer :: (Read a, Ring a) => String -> [Token a]
lexer [] = []
lexer ('x':xs) = Var : lexer xs
lexer ('^':xs) = let (n, rest) = span (`elem` ['0'..'9']) xs in Exp (read n) : lexer rest
lexer ('+':xs) = Plus : lexer xs
lexer xs = let (n, rest) = span (`elem` '-':['0'..'9']) xs in Coeff (read n) : lexer rest

-- The parse function processes the Tokens to build the Polynomial.
parse :: (Read a, Ring a) => [Token a] -> Polynomial a
parse tokens = go tokens 0 0 where
  go [] coeff exp = monomial coeff (fromInteger exp)
  go (Plus : ts) coeff exp = monomial coeff (fromInteger exp) + go ts 0 0
  go (Coeff c : ts) _ _ = go ts c 0
  go (Var : ts) coeff _ = go ts coeff 1
  go (Exp e : ts) coeff _ = go ts coeff e
  go _ _ _ = error "Invalid polynomial"


-- The parsePoly function combines the lexer and parse function to parse a String into a Polynomial.
parsePoly :: forall a. (Read a, Ring a) => String -> Polynomial a
parsePoly = parse . lexer

output :: (Show a, Ring a) => Maybe (Factoring (Polynomial a)) -> String
output (Just f) = show f
output _ = "(factoring failed)"

main :: IO ()
main = do
  args_ <- getArgs
  args <- if (length args_ > 1) then pure args_ else ( lines <$> readFile (args_ !! 0) )

  let showage = putStr . (foldr (\a b -> (a ++ "\n" ++ b)) "")

  case args of 
    "rational":t ->
      showage $ (output . factor . fmap toRational . parsePoly @Double) <$> t
    "integer":t ->
      showage $ (output . factor . parsePoly @Integer) <$> t
    "integer-mod":p:t ->
      showage $ reifyPrime (read p) (
        \(Proxy :: Proxy p) -> (output . factor . (<$>) (fromInteger @(PrimeField p)) . parsePoly @Integer) <$> t
      )
    _ ->
      error "Wrong number of arguments"