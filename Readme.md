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

Alternatively, use the command line tool.

```bash
cabal run exe:generic-polynomials -- integer 1x^4+-1x^0
```

the command line tool expects inputs like `ax^n+bx^m+...` any deviation from this will result in sadness.
