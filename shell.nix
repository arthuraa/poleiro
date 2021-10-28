{ pkgs ? import <nixpkgs> {} }:

with pkgs;

let coq = coq_8_13;
    coqPackages = coqPackages_8_13;
    ssreflect = coqPackages.mathcomp.ssreflect;
    algebra = coqPackages.mathcomp.algebra;
    ghc = haskellPackages.ghcWithPackages (pkgs:
      [ pkgs.hakyll ]
    );
    gems = bundlerEnv {
      name = "compass";
      gemdir = ./.;
    };
in

mkShell {
  LANG = "en_US.UTF-8";
  LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
  buildInputs = [ ghc coq ssreflect algebra gems gems.wrappedRuby ];
}
