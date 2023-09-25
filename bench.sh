#!/bin/bash

# Example script to benchmark Mathematica, SageMath, and a custom program

cabal build exe:generic-polynomials
module add /opt/modulefiles/applications/sage/9.2

cd benchmarks

cabal install --lib random
runghc -package --ghc-arg=random init.hs

cd ..

echo "Benchmarking Mathematica..."
(time wolfram -script benchmarks/test.m) 2> benchmarks/mathematica_time.txt
cat benchmarks/mathematica_time.txt

echo "Benchmarking SageMath..."
(time sage benchmarks/test.sage) 2> benchmarks/sagemath_time.txt
cat benchmarks/sagemath_time.txt

echo "Benchmarking Custom Program..."
(time cabal run exe:generic-polynomials -- integer-mod 13 $(<benchmarks/test.txt)) 2> benchmarks/custom_program_time.txt
cat benchmarks/custom_program_time.txt
