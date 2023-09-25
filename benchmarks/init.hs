import System.IO
import System.Random
import Control.Monad (replicateM)

-- Function to generate a random coefficient
randomCoefficient :: IO Int
randomCoefficient = getStdRandom (randomR (0, 100))

-- Function to generate a term of a polynomial
generateTerm :: Int -> IO String
generateTerm n_ = do
    n <- getStdRandom $ randomR (0, n_)
    coefficient <- randomCoefficient
    return $ show coefficient ++ "x^" ++ show n

-- Function to generate a polynomial of degree n
generatePolynomial :: Int -> IO String
generatePolynomial degree = do
    terms <- replicateM degree $ generateTerm degree
    return $ foldr (\a b -> a ++ " + " ++ b) "0" terms


createHaskell :: [String] -> IO ()
createHaskell lst = 
    writeFile "test.txt" contents
    where
        contents = foldr (++) ""  
            $ (flip (++) " " . noSpaces) <$> lst

        noSpaces [] = []
        noSpaces (' ':t) = noSpaces t
        noSpaces (h:t) = h:(noSpaces t)

createSage :: [String] -> IO ()
createSage lst = do
    writeFile "test.sage" contents
    where
        contents = (++) "R = PolynomialRing(GF(13), 'x')\n" 
            $ foldr (++) "" 
            $ (\p -> "R( " ++ withtimes p ++ " ).factor()\n") <$> lst
        
        withtimes [] = []
        withtimes ('x':t) = '*':'x':(withtimes t)
        withtimes (h:t) = h:(withtimes t)

createWolfram :: [String] -> IO ()
createWolfram lst = do
    writeFile "test.m" contents
    where
        contents = foldr (++) "" 
            $ (\p -> "Factor[ " ++ p ++ " , Modulus -> 13]\n") <$> lst

main :: IO ()
main = do
    lst <- sequence $ generatePolynomial <$> [1..10]
    createHaskell lst
    createSage lst
    createWolfram lst