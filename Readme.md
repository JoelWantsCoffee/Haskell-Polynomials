# Factoring Polynomials in Haskell

## Setup

install `nix`

clone repo

run `nix-shell`

## Usage

Use the `factor` function with type applicaiton to factor polynomials.

```haskell
factor @Integer (x^3 + x^2 + x + 1)
```

Currently, `Polynomial (PrimeField p)`, `Polynomial Integer`, and `Polynomial Rational` should work.
