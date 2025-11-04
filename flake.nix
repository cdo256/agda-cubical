{
  description = "";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } (top: {
      systems = [
        "x86_64-linux"
      ];
      perSystem =
        { pkgs, ... }:
        let
          agda = pkgs.agda.withPackages (ps: [ ]);
        in
        {
          devShells.default = pkgs.mkShell {
            buildInputs = [
              agda
              pkgs.ghc
              pkgs.gnumake
            ];
          };
        };
    });
}
