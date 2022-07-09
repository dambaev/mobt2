{pkgs ? {}}:
{
  ats-mobt2 = pkgs.callPackage ./derivation.nix {};
}
