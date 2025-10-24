{
  description = "";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    just-agda.url = "github:cdo256/just-agda";
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
          just-agda-base = inputs.just-agda.packages.${pkgs.system}.default;
          just-agda = just-agda-base.override { inherit agda; };
        in
        {
          packages = {
            inherit agda just-agda;
            default = just-agda;
          };
          devShells.default = pkgs.mkShell {
            buildInputs = [
              agda
              just-agda
              pkgs.ghc
              pkgs.gnumake
            ];
          };
        };
    });
}
