#!/bin/bash

# Example script to benchmark Mathematica, SageMath, and a custom program

cabal build exe:generic-polynomials
module add /opt/modulefiles/applications/sage/9.2

cabal install --lib random



# echo "Benchmarking Mathematica..."
# (time -p wolfram -script benchmarks/test.m) 2> benchmarks/mathematica_time.txt
# cat benchmarks/mathematica_time.txt

# echo "Benchmarking SageMath..."
# (time -p sage benchmarks/test.sage) 2> benchmarks/sagemath_time.txt
# cat benchmarks/sagemath_time.txt

# echo "Benchmarking Custom Program..."
# (time -p cabal run exe:generic-polynomials -- benchmarks/test.txt) 2> benchmarks/custom_program_time.txt
# cat benchmarks/custom_program_time.txt

time_command () {
    echo benchmark: $1 >> benchmarks/out.txt
    echo $( (time -p ($1 2>&1)) 2>&1 1>>benchmarks/out.txt | head -n 1 | cut -d' ' -f2 )
}

log_times () {
    cd benchmarks
    runghc -package --ghc-arg=random init.hs $1 $2 $3
    cd ..
    echo $1, $(time_command "wolfram -script benchmarks/test.m"), $(time_command "sage benchmarks/test.sage"), $(time_command "cabal run exe:generic-polynomials -- benchmarks/test.txt") | tee -a benchmarks/results.csv
}

# (time -p (cabal run exe:generic-polynomials -- benchmarks/test.txt 2>&1)) 2>&1 1>out.txt | head -n 1 | cut -d' ' -f2
echo benchmark: started... > benchmarks/out.txt
echo degree, Mathematica, SageMath, Haskell-Polynomials | tee benchmarks/results.csv
i=2
while [ $i -ne 11 ]
do
    log_times $i $1 $2
    i=$(($i+1))
done
# cabal run generic-polynomials --enable-profiling -- +RTS -p -RTS benchmarks/test.txt