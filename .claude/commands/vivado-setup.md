---
description: Create a new Vivado project with standard scaffolding
---

Create a new Vivado project for the SVC RISC-V ecosystem.

## Usage

```
/vivado-setup <board> <name> [--type rv-bram|rv-ddr3|minimal] [--float]
```

## Arguments

- `board`: Target board (currently: `arty_s7`)
- `name`: Project/application name (e.g., `hello`, `benchmark`)
- `--type`: Project type (default: `rv-bram`)
  - `rv-bram`: RISC-V SoC with BRAM memory (100 MHz)
  - `rv-ddr3`: RISC-V SoC with DDR3/cache (85.25 MHz, requires MIG setup)
  - `minimal`: Basic skeleton without RISC-V
- `--float`: Enable F extension (adds fpnew FPU and related source files)

## Examples

```bash
# Simple BRAM-based RISC-V project (default)
/vivado-setup arty_s7 hello

# RISC-V project with floating-point support
/vivado-setup arty_s7 pi --float

# DDR3-backed RISC-V project for benchmarks
/vivado-setup arty_s7 benchmark --type rv-ddr3

# Minimal skeleton for custom design
/vivado-setup arty_s7 uart_test --type minimal
```

## Output Structure

Creates `vivado/<board>_rv_<name>/` (or `<board>_<name>` for minimal):

```
vivado/<project>/
  rtl/top.sv
  constraints/<board>.xdc
  vivado/create_project.tcl
  .gitignore
```

## Next Steps

After running the command:

1. Build software: `make sw/<name>`
2. Open Vivado:
   `cd vivado/<project>/vivado && vivado -source create_project.tcl`

Run the vivado-setup script:

```bash
svc/scripts/vivado-setup $ARGUMENTS
```
