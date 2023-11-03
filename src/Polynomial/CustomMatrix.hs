module Polynomial.CustomMatrix where

import Polynomial.Ring
import Data.List
import Data.Maybe

-- THIS FILE WAS WRITTEN BY CHATGPT

scaleRow :: (Field a) => a -> [a] -> [a]
scaleRow _ [] = []
scaleRow 0 _ = error "Cannot scale by zero"
scaleRow s xs = map ((*) (inv s)) xs

zeroOut :: (Field a) => a -> [a] -> [a] -> [a]
zeroOut _ [] _ = []
zeroOut factor (x:xs) (y:ys) = (x - factor * y) : zeroOut factor xs ys
zeroOut _ _ _ = error "matrix : zeroOut function"

findPivot :: (Field a) => [a] -> Maybe Int
findPivot = findIndex (/=0)

rowReduction :: (Field a) => [[a]] -> [[a]]
rowReduction [] = []
rowReduction mat_ = foldr reduceRow mat_ [0..length mat_ - 1]
    where
        reduceRow r mat
            | r >= length mat = mat
            | otherwise =
                let row = mat !! r
                    pivotPos = findPivot row
                in case pivotPos of
                    Nothing -> mat
                    Just p ->
                        let pivot = row !! p
                            scaledRow = scaleRow pivot row
                            mat' = map (\x -> if x == r then scaledRow else (mat !! x)) [0..length mat - 1]
                            mat'' = map (\x -> if x == r then mat' !! x else zeroOut (mat' !! x !! p) (mat' !! x) scaledRow) [0..length mat - 1]
                        in mat''

gaussianJordanElimination :: (Field a) => [[a]] -> [[a]]
gaussianJordanElimination mat = reverse $ rowReduction $ reverse $ rowReduction mat

-- Function to identify the free variables in the matrix
findFreeVars :: (Field a) => [[a]] -> [Int]
findFreeVars rref = 
    let numRows = length rref
        numCols = length (head rref)
        pivotCols = nub $ mapMaybe findPivot rref  -- get the unique pivot columns
        allCols = [0..numCols - 1]
    in allCols \\ pivotCols  -- set difference to get the free variable columns

-- Function to generate a nullspace vector for a given free variable
generateNullspaceVector :: (Field a) => [[a]] -> Int -> [a]
generateNullspaceVector rref freeVarIndex =
    let numCols = length (head rref)
    in [ if col == freeVarIndex then 1 else 0 | col <- [0..numCols-1] ]

-- Main function to find a basis for the nullspace
nullspaceBasis :: (Field a) => [[a]] -> [[a]]
nullspaceBasis mat = 
    let rref = gaussianJordanElimination mat
        freeVars = findFreeVars rref
    in map (generateNullspaceVector rref) freeVars

multiply :: (Ring a) => [[a]] -> [a] -> [a]
multiply mat vec = (sum . zipWith (*) vec) <$> mat