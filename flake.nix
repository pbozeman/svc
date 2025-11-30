{
  description = "Verilog dev env";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      ...
    }@inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        verilog-vcd = pkgs.python3Packages.buildPythonPackage rec {
          pname = "Verilog_VCD";
          version = "1.11";

          src = pkgs.python3Packages.fetchPypi {
            inherit pname version;
            # temporary hash; nix will tell you the real one
            sha256 = "sha256-L/peNxHFfRMS3EEaGRih+PFx/xDwQ8d0n7Epq3ZCaDo=";
          };

          doCheck = false;
        };

        # Python package with required dependencies
        pythonEnv = pkgs.python3.withPackages (
          ps: with ps; [
            jinja2
            pyserial
            verilog-vcd
          ]
        );

        # Base build inputs common to all systems
        baseBuildInputs = with pkgs; [
          boolector
          flock
          gtkwave
          icestorm
          nextpnr
          nodePackages.prettier
          pkgs.pkgsCross.riscv64-embedded.buildPackages.gcc
          pythonEnv
          sby
          socat
          verilator
          verilog
          yices
          yosys
        ];

        # Conditionally add packages if the system is not Darwin
        buildInputs =
          baseBuildInputs
          ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
            # these packages don't work correctly on Darwin
            pkgs.verible
            pkgs.xdot
          ];
      in
      {
        devShell = pkgs.mkShell {
          inherit buildInputs;
        };
      }
    );
}
