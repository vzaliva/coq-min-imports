{ pkgs, version ? null, ... }:

{ coq-min-imports =
    pkgs.ocamlPackages.buildDunePackage rec {
      pname = "coq-min-imports";
      inherit version;
      useDune2 = true;
      src = ./.;

      buildInputs = with pkgs.ocamlPackages;
        [ ocaml_extlib batteries ];

      meta = with pkgs.lib; {
        homepage = "https://github.com/vzaliva/coq-min-imports";
        description = "Script to remove unnecessary module imports from Coq sources.";
        license = licenses.mit;
      };
    };
}
