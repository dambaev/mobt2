let
#  pkgs = import /data/devel/nixpkgs/default.nix {};
  pkgs = import <nixpkgs> {  };
in
  pkgs.haskellPackages.callPackage ./default.nix { }
