{ stdenv, pkgs, fetchzip, fetchpatch, fetchgit, fetchurl }:
stdenv.mkDerivation {
  name = "ats-mobt2";

  src = ./. ;
  buildInputs = with pkgs;
  [ ats2
  ];

}
