let pkgs =import <nixpkgs> {}; 
in
with pkgs;

stdenv.mkDerivation {
  name = "certikos";

  buildInputs = with ocamlPackages_4_02; [
    camlp4
    ocaml menhir findlib coq_8_6
    coqPackages_8_6.flocq
  ];

}