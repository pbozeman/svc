# SVC - SystemVerilog Core: Claude Coding Guide

This file contains essential information for AI assistants (Claude) to
effectively write and modify code in the SVC repository.

## Repository Structure

Modules are organized functionally under `rtl/`:

- **rtl/axi/** - AXI/AXI-Lite bus infrastructure
- **rtl/cdc/** - Clock Domain Crossing
- **rtl/common/** - Fundamental building blocks
- **rtl/fifo/** - Synchronous FIFOs
- **rtl/gfx/** - Graphics and VGA
- **rtl/ice40/** - iCE40 FPGA-specific
- **rtl/rv/** - RISC-V processor
- **rtl/stats/** - Statistics collection
- **rtl/uart/** - Serial communication

Testbenches mirror this structure under `tb/` (e.g., `tb/axi/`, `tb/common/`).
Formal verification files are in `tb/formal/` (flat directory).

## Core Documentation

- **[docs/style.md](docs/style.md)** - CRITICAL: Read this for all coding
  conventions
- **[docs/tb.md](docs/tb.md)** - Testbench patterns and framework
- **Module READMEs** - Each rtl/ subdirectory has a README.md with module
  organization

## Build Commands

### Standard Workflow

```bash
make quick    # Default: tests + formal with success silencing
make full     # Full verification with linting
make tb       # Run all testbenches
make formal   # Run all formal verification
make lint     # Lint with Verilator
make format   # Format all code (ALWAYS RUN AFTER CHANGES)
```

### Single Module Testing

```bash
make <module_name>_tb    # Run testbench (e.g., make svc_arbiter_tb)
make <module_name>_f     # Run formal verification (e.g., make svc_arbiter_f)
make list_tb             # List all testbench targets
make list_f              # List all formal targets
```

## Critical Style Rules

### Comments

- **NEVER use end-of-line comments** - ALL comments must be on the line above
- Use blank comment separators for sections:

```systemverilog
//
// Section description
//
```

### File Organization

- **New modules**: Place in appropriate rtl/ subdirectory based on function
- **New testbenches**: Place in corresponding tb/ subdirectory
- **Include guards**: Always use `ifndef`/`define`/`endif` with `_SV` suffix
- **svc.sv include**: Always include after guard definition

### Naming

- **Modules**: `svc_` prefix for all modules
- **Reset**: Always `rst_n` (active-low)
- **Clock**: Always `clk`
- **Next-cycle signals**: `_next` suffix
- **Pipeline stages**: `_p1`, `_p2` suffixes
- **Interfaces**: `s_` for subordinate, `m_` for manager

### State Machines

- Use `typedef enum` without explicit bit width
- Prefix states with `STATE_` (or `READ_STATE_`/`WRITE_STATE_` if multiple FSMs)
- Separate always_ff for transitions, always_comb for outputs

### Code Structure

1. Localparams
2. Internal signals
3. Child module instantiations
4. Combinational logic (always_comb)
5. Sequential logic (always_ff)
6. Formal assertions (if applicable)

## Common Patterns

### Reset Pattern

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) begin
    counter <= '0;
    state   <= STATE_IDLE;
  end else begin
    counter <= counter_next;
    state   <= state_next;
  end
end
```

### Valid-Ready Handshake

```systemverilog
//
// Combinational logic
//
always_comb begin
  out_valid = data_available && !blocked;
  in_ready  = !full && !blocked;
end

//
// Transfer on handshake
//
always_ff @(posedge clk) begin
  if (out_valid && out_ready) begin
    // Process transfer
  end
end
```

## Testbench Requirements

- **Framework**: Use `svc_unit.sv` (in rtl/common/)
- **First test**: Always include a reset test
- **File location**: Place in tb/ subdirectory matching module's rtl/ location
- **Naming**: `<module_name>_tb.sv` suffix
- **Structure**: See docs/tb.md for complete template

### Key Macros

```systemverilog
// Clock and reset
`TEST_CLK_NS(clk, 10);
`TEST_RST_N(clk, rst_n);

// Assertions
`CHECK_TRUE(condition);
`CHECK_EQ(a, b);
`CHECK_WAIT_FOR(clk, condition, max_cycles);

// Test organization
`TEST_SUITE_BEGIN(module_name_tb);
`TEST_CASE(test_function);
`TEST_SUITE_END();
```

## Workflow Checklist

When writing or modifying code:

1. ✅ Read docs/style.md for conventions
2. ✅ Check existing similar modules for patterns
3. ✅ Place files in correct rtl/ or tb/ subdirectory
4. ✅ Follow naming conventions (svc\_ prefix, rst_n, etc.)
5. ✅ Comments above lines, never at end of line
6. ✅ Use blank comment blocks for section separation
7. ✅ Run `make format` after ALL changes
8. ✅ Run `make lint` before committing
9. ✅ Test with `make <module>_tb` and/or `make <module>_f`
10. ❌ NEVER add Co-Authored-By in commit messages

## Common Modules to Reference

- **Basic FIFO**: rtl/fifo/svc_sync_fifo.sv
- **AXI arbiter**: rtl/axi/svc_axi_arbiter.sv
- **Graphics**: rtl/gfx/svc_gfx_vga.sv
- **RISC-V processor**: rtl/rv/svc_rv.sv
- **RISC-V SoC**: rtl/rv/svc_rv_soc_bram.sv
- **Testbench example**: tb/common/svc_arbiter_tb.sv

## Key Principles

1. **Consistency**: Follow existing code patterns exactly
2. **Simplicity**: Keep logic clear and well-structured
3. **Verification**: Every module needs testbench and/or formal verification
4. **Documentation**: Use comments for complex logic, blank separators for
   sections
5. **Active-low reset**: Always use `rst_n`, never active-high reset
