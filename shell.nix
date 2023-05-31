{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.haskellPackages.ghc
    pkgs.haskellPackages.cabal-install
    pkgs.haskellPackages.stack
    pkgs.haskellPackages.either
    pkgs.haskellPackages.matrix
    # pkgs.haskellPackages.hmatrix
    pkgs.git
  ];

  shellHook = ''
    export LANG="en_US.UTF-8"
    export LC_ALL="en_US.UTF-8"
    export GHC_COLORS="always"
    cabal install matrix --lib --force-reinstalls
    cabal install either --lib --force-reinstalls
    echo "Entering Haskell Nix Shell"
  '';
}