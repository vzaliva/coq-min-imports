{
  description = "Script to remove unnecessary module imports from Coq sources.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        version = "coq-min-imports:master";
      in rec {
        packages = {
          default = (pkgs.callPackage ./release.nix { inherit version pkgs; }).coq-min-imports;
        };
      });
}
