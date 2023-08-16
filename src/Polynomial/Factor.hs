{-# LANGUAGE DataKinds #-}

module Polynomial.Factor 
    ( Ring(..)
    , GCDD(..)
    , UFD(..)
    , Field(..)
    , Prime
    , KnownPrime
    , PrimeField
    , FiniteCyclicRing
    , primeVal
    , factor
    , listify
    , unfactor
    , x
    )
where

import Polynomial.Polynomial
import Polynomial.Ring
import Polynomial.Squarefree
import Polynomial.Berlekamp()
import Polynomial.Hensel()



x :: Ring r => Polynomial r
x = monomial 1 1