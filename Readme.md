# Factoring Polynomials in Haskell

## Setup

install `nix`

clone repo

run `nix-shell`

## Usage

Use the `Factorable` typeclass to factor polynomials.

```haskell
class Factorable a where
    factor :: a -> [a]
```

Currently, `Polynomial (PrimeField p)` is the only instance.