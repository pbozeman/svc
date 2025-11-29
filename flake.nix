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

        # pyboolector for pyvsc constraint solving
        pyboolector = pkgs.python3Packages.buildPythonPackage rec {
          pname = "pyboolector";
          version = "3.2.4.19342042739";
          format = "wheel";

          src = pkgs.fetchurl {
            url = "https://files.pythonhosted.org/packages/4e/bf/a5d1747087551bfdd884e2b9540f9840e1c5a588959fa2084e5cb4426944/pyboolector-3.2.4.19342042739-cp312-cp312-manylinux_2_24_x86_64.manylinux_2_28_x86_64.whl";
            sha256 = "sha256-DeIhXxFEpM+f9e5mDvlE2znnpMJk5Q2/PU0qq+SIq5s=";
          };

          nativeBuildInputs = [ pkgs.autoPatchelfHook ];

          buildInputs = [ pkgs.stdenv.cc.cc.lib ];

          doCheck = false;
        };

        # python-jsonschema-objects for pyucis
        python-jsonschema-objects = pkgs.python3Packages.buildPythonPackage rec {
          pname = "python_jsonschema_objects";
          version = "0.5.7";

          src = pkgs.python3Packages.fetchPypi {
            inherit pname version;
            sha256 = "sha256-CvGp/SB6MVinO6qJUlbODukbuZxfkrB/1PrG/20AfJA=";
          };

          propagatedBuildInputs = with pkgs.python3Packages; [
            jsonschema
            inflection
            markdown
          ];

          doCheck = false;
        };

        # pyucis for pyvsc coverage support
        pyucis = pkgs.python3Packages.buildPythonPackage rec {
          pname = "pyucis";
          version = "0.1.4.18685268604";
          format = "wheel";

          src = pkgs.fetchurl {
            url = "https://files.pythonhosted.org/packages/a2/58/3f8612fa9569f26f8c32a6fcde59ddf337ed1eddd4f78013052e521536cf/pyucis-0.1.4.18685268604-py2.py3-none-any.whl";
            sha256 = "sha256-FcOs4RzPKI0a8hO+9dQBX+A84jTKoGqJFFbUv/Kx/dU=";
          };

          propagatedBuildInputs = [
            python-jsonschema-objects
          ];

          doCheck = false;
        };

        # pyvsc for riscv-dv constraint random generation
        pyvsc = pkgs.python3Packages.buildPythonPackage rec {
          pname = "pyvsc";
          version = "0.9.4.19475493160";
          format = "wheel";

          src = pkgs.fetchurl {
            url = "https://files.pythonhosted.org/packages/19/c1/409fa3aa980c5fa28636fd0fcd3731c57551f9be5b4875017aac2ebd1d91/pyvsc-0.9.4.19475493160-py2.py3-none-any.whl";
            sha256 = "sha256-f76F6G6v1MNaMb3+bly+itAJgs0G5nJz64GnixHyR58=";
          };

          propagatedBuildInputs = with pkgs.python3Packages; [
            pyboolector
            pyucis
            toposort
          ];

          doCheck = false;
        };

        # Python package with required dependencies
        pythonEnv = pkgs.python3.withPackages (
          ps: with ps; [
            bitstring
            lxml
            pandas
            pyvsc
            pyserial
            pyyaml
            tabulate
            verilog-vcd
          ]
        );

        # Base build inputs common to all systems
        baseBuildInputs = with pkgs; [
          boolector
          dtc
          flock
          gtkwave
          icestorm
          nextpnr
          nodePackages.prettier
          pkgs.pkgsCross.riscv64-embedded.buildPackages.gcc
          pythonEnv
          sby
          socat
          spike
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
