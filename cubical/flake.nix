{
  description = "Cubical Agda";

  inputs.nixpkgs.url = "nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  inputs.agda = {
    url = "github:agda/agda/v2.6.4.1";
    inputs = {
      nixpkgs.follows = "nixpkgs";
      flake-utils.follows = "flake-utils";
    };
  };
  inputs.just-agda = {
    type = "github";
    owner = "cdo256";
    repo = "just-agda";
    ref = "main";
  };

  outputs =
    {
      self,
      flake-compat,
      flake-utils,
      nixpkgs,
      agda,
      just-agda,
    }:
    let
      just-agda-input = just-agda;
      inherit (nixpkgs.lib) cleanSourceWith hasSuffix;
      overlay = final: prev: {
        cubical = final.agdaPackages.mkDerivation rec {
          pname = "cubical";
          version = "0.7";

          src = cleanSourceWith {
            filter = name: type: !(hasSuffix ".nix" name);
            src = ./.;
          };

          LC_ALL = "C.UTF-8";

          # The cubical library has several `Everything.agda` files, which are
          # compiled through the make file they provide.
          nativeBuildInputs = [ final.ghc ];
          buildPhase = ''
            make
          '';
          meta = {
            description = "An experimental library for Cubical Agda";
            homepage = "https://github.com/agda/cubical";
            license = "MIT License";
          };
        };
        agdaWithCubical = final.agdaPackages.agda.withPackages [ final.cubical ];
        just-agda = just-agda-input.packages.${prev.system}.just-agda
        #  .override {
        #  inherit agda;
        #  inherit (prev.emacsPackages) agda2-mode;
        #};
        ;
      };
      overlays = [
        agda.overlay
        overlay
      ];
    in
    {
      overlays.default = overlay;
    }
    // flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system overlays; };
      in
      rec {
        packages = with pkgs; rec {
          inherit cubical agdaWithCubical;
          default = cubical;
          just-agda = just-agda.packages.${system}.just-agda.override {
            inherit agda;
            inherit (pkgs.emacsPackages) agda2-mode;
          };
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.agda
            pkgs.just-agda
            pkgs.texlab
            pkgs.ltex-ls
            pkgs.pandoc
            pkgs.fira-mono
            pkgs.dejavu_fonts
            pkgs.fontconfig
            pkgs.julia-mono
          ];
        };
      }
    );
}
