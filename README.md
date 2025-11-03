# SVC - SystemVerilog Core

A collection of reusable SystemVerilog modules with comprehensive verification
and an integrated build system supporting unit testing, formal verification, and
FPGA synthesis.

## Repository Structure

### RTL Modules (rtl/)

Modules are organized functionally:

- **axi/** - AXI/AXI-Lite bus infrastructure (arbiters, routers, adapters,
  memory controllers)
- **cdc/** - Clock Domain Crossing (synchronizers, async FIFOs)
- **common/** - Fundamental building blocks (arbiters, delays, edge detection,
  skid buffers)
- **fifo/** - Synchronous FIFOs (FWFT and zero-latency variants)
- **gfx/** - Graphics and VGA (framebuffers, line drawing, VGA timing)
- **ice40/** - iCE40 FPGA-specific implementations (PLLs, SRAM interfaces)
- **rv/** - RISC-V processor (RV32I, single or 5-stage pipeline, configurable)
- **stats/** - Statistics collection (counters, min/max trackers)
- **uart/** - Serial communication (TX/RX, formatted printing)

### Verification (tb/)

- Testbenches in subdirectories mirroring rtl/ structure
- Formal verification files in `tb/formal/` using SymbiYosys
- Custom `svc_unit` testing framework for simulation

## Build Commands

```bash
make quick    # Run tests and formal verification (default)
make full     # Full verification with linting
make tb       # Run all testbenches
make formal   # Run all formal verification
make lint     # Lint all code with Verilator
make format   # Format all code
```

### Single Module Testing

```bash
make <module>_tb       # Run specific testbench (e.g., make svc_arbiter_tb)
make <module>_f        # Run formal verification (e.g., make svc_arbiter_f)
make list_tb           # List available testbench targets
make list_f            # List available formal targets
```

## Verification

Modules use multiple verification approaches:

- Unit testing with simulation testbenches
- Formal verification with bounded model checking
- Static analysis with Verilator linting

AXI modules can optionally use ZipCPU formal verification IP (Patreon-only).
Place ZipCPU formal files in `tb/formal/private/` directory. (It is excluded by
.gitignore)
