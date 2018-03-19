# You can build this repository using Nix by running:
#
#     $ nix-build -A morte release.nix
#
# You can also open up this repository inside of a Nix shell by running:
#
#     $ nix-shell -A morte.env release.nix
#
# ... and then Nix will supply the correct Haskell development environment for
# you
let
  config = {
    packageOverrides = pkgs: {
      haskellPackages = pkgs.haskellPackages.override {
        overrides = haskellPackagesNew: haskellPackagesOld: {
          morte = haskellPackagesNew.callPackage ./default.nix { };

          formatting = haskellPackagesNew.callPackage ./formatting.nix { };
        };
      };
    };
  };

  pkgs =
    import <nixpkgs> { inherit config; };

in
  { morte = pkgs.haskellPackages.morte;
  }
