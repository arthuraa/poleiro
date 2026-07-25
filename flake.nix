{
  description = "Poleiro development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem = { pkgs, lib, ... }:
        let
          coq = pkgs.coq_8_13;
          coqPackages = pkgs.coqPackages_8_13;
          ssreflect = coqPackages.mathcomp.ssreflect;
          algebra = coqPackages.mathcomp.algebra;

          ghc = pkgs.haskellPackages.ghcWithPackages (ps: [ ps.hakyll ]);

          # The pinned sass/compass gems still call File.exists?, which was
          # removed in Ruby 3.2, so build them against Ruby 3.1.
          gems = pkgs.bundlerEnv {
            name = "compass";
            ruby = pkgs.ruby_3_1;
            gemdir = ./.;
          };
        in
        {
          devShells.default = pkgs.mkShell ({
            packages = [
              ghc
              coq
              ssreflect
              algebra
              gems
              gems.wrappedRuby
            ];

            LANG = "en_US.UTF-8";
          } // lib.optionalAttrs pkgs.stdenv.isLinux {
            LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          });
        };
    };
}
