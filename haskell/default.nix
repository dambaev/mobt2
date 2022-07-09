{ mkDerivation, base, containers, fused-effects, hspec, posix-pty
, process, stdenv, streamly, text, fused-effects-exceptions
}:
mkDerivation {
  pname = "mobt2";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers
  ];
  executableHaskellDepends = [ base ];
  testHaskellDepends = [ base hspec text ];
  license = stdenv.lib.licenses.bsd3;
}
