module CustomMatrix where

import Data.List

-- THIS FILE WAS WRITTEN BY CHATGPT

scaleRow :: (Fractional a, Eq a) => a -> [a] -> [a]
scaleRow _ [] = []
scaleRow 0 _ = error "Cannot scale by zero"
scaleRow s xs = map (/s) xs

zeroOut :: (Fractional a, Eq a) => a -> [a] -> [a] -> [a]
zeroOut _ [] _ = []
zeroOut factor (x:xs) (y:ys) = (x - factor * y) : zeroOut factor xs ys

findPivot :: (Fractional a, Eq a) => [a] -> Maybe Int
findPivot = findIndex (/=0)

rowReduction :: (Fractional a, Eq a) => [[a]] -> [[a]]
rowReduction [] = []
rowReduction mat = foldr reduceRow mat [0..length mat - 1]
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

gaussianJordanElimination :: (Fractional a, Eq a) => [[a]] -> [[a]]
gaussianJordanElimination mat = reverse $ rowReduction $ reverse $ rowReduction mat
