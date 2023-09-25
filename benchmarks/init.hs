import System.IO
import System.Random
import System.Environment
import Control.Monad (replicateM)

data Domain = Ints | Rats | Mods Integer

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


createHaskell :: Domain -> [String] -> IO ()
createHaskell d lst = 
    writeFile "test.txt" contents
    where
        contents = (++) (
                case d of
                    Mods n -> "integer-mod\n" ++ show n ++ "\n"
                    Rats -> "rational\n"
                    Ints -> "integer\n"
                )
            $ foldr (++) ""  
            $ (flip (++) "\n" . noSpaces) <$> lst

        noSpaces [] = []
        noSpaces (' ':t) = noSpaces t
        noSpaces (h:t) = h:(noSpaces t)

createSage :: Domain -> [String] -> IO ()
createSage d lst = do
    writeFile "test.sage" contents
    where
        contents = (++) ("R = PolynomialRing( " ++ (case d of
            Mods n -> "GF(" ++ show n ++ ")"
            Ints -> "ZZ"
            Rats -> "QQ"
            ) ++ " , 'x')\n") 
            $ foldr (++) "" 
            $ (\p -> "R( " ++ withtimes p ++ " ).factor()\n") <$> lst
        
        withtimes [] = []
        withtimes ('x':t) = '*':'x':(withtimes t)
        withtimes (h:t) = h:(withtimes t)

createWolfram :: Domain -> [String] -> IO ()
createWolfram d lst = do
    writeFile "test.m" contents
    where
        contents = foldr (++) "" 
            $ (\p -> "Factor[ " ++ p ++ (case d of
                    Mods n -> " , Modulus -> " ++ show n
                    _ -> " "
                ) ++ "]\n") <$> lst

main :: IO ()
main = do
    args <- getArgs
    let dom = ( case args of 
            _:"rational":_ -> Rats
            _:"integer":_ -> Ints
            _:"integer-mod":p:_ -> Mods (read p)
            _ -> error "domain not (correctly) specified."
            )
    lst <- sequence $ generatePolynomial <$> (\_ -> read @Int (args!!0)) <$> [1..100]
    createHaskell dom lst
    createSage dom lst
    createWolfram dom lst