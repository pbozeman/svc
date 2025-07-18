{
  description = "Verilog dev env";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        # Python package with required dependencies
        pythonEnv = pkgs.python3.withPackages (ps: with ps; [
          mdformat-gfm
          pyserial
        ]);

        # Base build inputs common to all systems
        baseBuildInputs = with pkgs; [
          boolector
          flock
          gtkwave
          icestorm
          mdformat
          nextpnr
          pythonEnv
          sby
          socat
          verilator
          verilog
          yices
          yosys
        ];

        # Conditionally add packages if the system is not Darwin
        buildInputs = baseBuildInputs ++
          pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
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
