{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    Agda.url = "github:fredins/agda";
    Agda.flake = true;
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];

      perSystem = { self', pkgs, ... }: {
        haskellProjects.default = {
          packages = {
            Agda.source = inputs.Agda;
          };

          settings = {
            Agda.check = false;
          };

          devShell = {
            enable = true;
            hlsCheck = true;
            tools = hp: { 
            };
          };
        };

        packages.default = self'.packages.agda-llvm;
      };
    };
}
