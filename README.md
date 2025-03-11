# SVC - System Verilog Core

This is a repo of common System Verilog modules, plus an opinionated build
system. The build system performs unit testing, formal verification, and
bitstream generation and programming.

Modules are unit tested with the included svc_unit testing framework, and some
are formally verified with SymbiYosys. Formal verification is currently only
using bounded model checking, with inductive proofs to be done in the future.
AXI modules are optionally verified using the private ZipCPU AXI verification
modules available to ZipCPU Patreon supporters.
