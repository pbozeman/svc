# SVC - Shared Agent Instructions

## Chat Formatting

In ALL chat responses, use backticks for ANY text containing underscores:

- File names: `svc_unit.sv`
- Macro names: `TEST_SUITE_BEGIN`, `CHECK_EQ`
- Signal names: `axi_arvalid`

For SystemVerilog code with preprocessor syntax (backtick-define,
backtick-ifdef, macro expansions), use fenced code blocks instead of inline
backticks:

```systemverilog
    `define VGA_MODE_H_SYNC_START (`VGA_MODE_H_VISIBLE + `VGA_MODE_H_FRONT_PORCH)
```

Never put SV preprocessor code inline -- the backticks conflict with Markdown.

## Project Structure

Modules organized functionally under `rtl/`:

- `rtl/axi/` - AXI/AXI-Lite bus infrastructure
- `rtl/cdc/` - Clock Domain Crossing
- `rtl/common/` - Fundamental building blocks
- `rtl/fifo/` - Synchronous FIFOs
- `rtl/gfx/` - Graphics and VGA
- `rtl/ice40/` - iCE40 FPGA-specific
- `rtl/rv/` - RISC-V processor
- `rtl/stats/` - Statistics collection
- `rtl/uart/` - Serial communication

Testbenches mirror under `tb/`. Formal verification in `tb/formal/` (flat).

Each `rtl/` subdirectory has a README.md with module details.

## Build Commands

```bash
make quick           # Default: tests + formal (silenced on success)
make full            # Full verification with linting
make <module>_tb     # Single testbench (e.g., make svc_arbiter_tb)
make <module>_f      # Single formal (e.g., make svc_arbiter_f)
make format          # Format all code - ALWAYS RUN AFTER CHANGES
make lint            # Lint with Verilator
make list_tb         # List all testbench targets
make list_f          # List all formal targets
```

## Things NOT To Do

- NEVER run `sby` directly - always use `make <module>_f`
- NEVER add Co-Authored-By in commit messages
- NEVER use end-of-line comments - all comments on line above

## Skills

Shared skills live in `docs/skills/` and are symlinked into `.claude/skills` and
`.codex/skills`.
