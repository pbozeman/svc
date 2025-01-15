# SVC - System Verilog Core

This is a repo of common System Verilog modules, plus an opinionated
build system. The build system performs unit testing, formal verification,
and bitstream generation and programming.

The modules are unit tested with the included svc_unit testing framework,
and formally verified with SymbiYosys. AXI modules are optionally verified
using the private ZipCPU AXI verification modules available to ZipCPU Patreon
supporters.
