let pkgs =import <nixpkgs> {}; 
in
with pkgs;

stdenv.mkDerivation {
  name = "compcert-3.1";

  buildInputs = with ocamlPackages; [
    ocaml menhir findlib coq_8_6 compcert
  ];

}
