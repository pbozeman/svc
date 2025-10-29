# SVC SystemVerilog Style Guide

This document outlines the coding style standards for the SVC (SystemVerilog
Core) library, as well as guidelines for contributing to the codebase. The guide
is intended for both human contributors and AI tools like Claude.

## Module Style

### Include Guards and Headers

```systemverilog
`ifndef MODULE_NAME_SV
`define MODULE_NAME_SV

`include "svc.sv"

// Module code here

`endif
```

- Use `ifndef`/`define`/`endif` include guards with the module name in uppercase
  followed by \_SV
- Always add `include "svc.sv"` after the include guard definition
- Include all dependent modules before the module declaration

### Module Declaration

```systemverilog
module svc_example #(
    parameter WIDTH = 32,
    parameter DEPTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,

    input  logic             in_valid,
    input  logic [WIDTH-1:0] in_data,
    output logic             in_ready,

    output logic             out_valid,
    input  logic             out_ready,
    output logic [WIDTH-1:0] out_data
);
```

- Use module prefix `svc_` for all modules
- Place parameters before ports in module declarations
- Group related ports together with a blank line separating groups
- Align port declarations for readability

### Module Structure

1. Declare all localparams after the module declaration
1. Declare all internal signals
1. Instantiate child modules
1. Define combinational logic (always_comb blocks)
1. Define sequential logic (always_ff blocks)
1. Add assertions if using formal verification

## Naming Conventions

### Modules and Files

- **Module naming**: Use `svc_` prefix for all modules
- **Testbench suffix**: Use `_tb` suffix for testbenches
- **Formal verification suffix**: Use `_f` suffix for formal verification
- **RTL files**: Place in appropriate `rtl/` subdirectory (axi, cdc, common,
  fifo, gfx, ice40, stats, uart)
- **Testbench files**: Place in corresponding `tb/` subdirectory mirroring RTL
  organization
- **Formal verification files**: Place formal verification in `tb/formal/`
  directory

### Signals

- **Signal naming**: Use lower snake_case without input/output prefixes
- **Clock signal**: Name as `clk`
- **Reset signal**: Always use active-low reset as `rst_n`
- **Next-cycle signals**: Use `_next` suffix (e.g., `grant_valid_next`)
- **Pipeline stage signals**: Use `_p1`, `_p2` suffixes for signals in pipeline
  stages
- **Interface signals**:
  - Use `valid`/`ready` for stream interfaces
  - Use `start`/`done` for multi-cycle operations
  - Prefix with `s_` for slave interfaces and `m_` for master interfaces

## Language Features

### Types and Assignments

- Use `logic` instead of `wire`/`reg`
- Use synchronous active-low reset (`rst_n`) in all sequential blocks
- Use always_ff with non-blocking assignments (`<=`) for sequential logic
- Use always_comb with blocking assignments (`=`) for combinational logic
- Use proper type casting instead of disabling lint warnings
- For complex conditionals, use if/else blocks instead of ternary operators

### Signal Declarations

- Declare each signal on a separate line, never group declarations
- Add new lines between logical groupings of declarations and assignments
- Keep signal widths in brackets aligned for readability:

```systemverilog
logic [  ADDR_WIDTH:0] ptr;
logic [DATA_WIDTH-1:0] data;
```

### Code Organization

- Add blank lines between logical sections of code
- Use meaningful signal names that reflect their purpose
- Define combinational blocks first, followed by sequential blocks
- Group related functionality together

## Comments and Documentation

- NEVER use end-of-line comments - ALL comments must be placed on the line above
  the code
- Add meaningful comments for complex logic
- Document parameters and their valid ranges
- Use blank comment lines to separate logical sections:

```systemverilog
//
// Write pointer logic
//
```

## AXI/AXI-Lite Interface Standards

- Follow standard AXI/AXI-Lite signal naming conventions
- Group AXI channels (AW, W, B, AR, R) together
- Maintain standard channel ordering (AW, W, B, AR, R)
- Follow burst, size, and other AXI parameters specifications

## State Machines

- Use type enum for state definitions with meaningful state names
- Do not define the logic bit width in the typedef
- Prefix each enum value with STATE.
- If there are multiple state machines in same module, give each names like
  WRITE_STATE_IDLE for write_state_t , READ_STATE_IDLE for read_state_t

```systemverilog
typedef enum {
  STATE_IDLE,
  STATE_BUSY,
  STATE_DONE,
  STATE_ERROR
} state_t;
```

- Use a single always_ff block for state transitions
- Use a separate always_comb block for output logic

## Graphics-Specific Guidelines

- For line drawing implementations, use fixed-width math to avoid truncation
  issues
- Use start/done control interfaces for graphics operations that take multiple
  cycles
- Ensure registers are properly sized for pixel coordinates to avoid overflow
- Use consistent color values (12'hF00 for red, 12'h0F0 for green, etc.) in
  tests

## Testbench-Specific Guidelines

- Refer to `docs/tb.md` for detailed testbench guidelines
- Use the `svc_unit.sv` framework for all testbenches
- Always include a reset test as the first test
- Verify proper behavior with backpressure in streaming interfaces

## Formal Verification Guidelines

- Create separate SBY files for formal verification
- Add formal properties in the RTL module if applicable
- Use appropriate assumptions and assertions
- Verify properties for at least 20 cycles

## AI-Assisted (Claude) Contribution Guidelines

When using Claude to generate or modify code, follow these additional
guidelines:

1. **Consistency**: Claude should strictly adhere to the style conventions of
   existing code
1. **NEVER add Co-Authored-By blocks in commit messages** - this policy is
   strictly enforced

### Workflow for Claude

1. Analyze existing modules to understand the codebase's conventions
1. Follow the same patterns for signal naming, module organization, and code
   style
1. After generating code, verify it complies with all style guidelines
1. Always run `make format` after generating new code to ensure consistent
   formatting
1. Verify linting passes with `make lint` before committing any changes

## Common Patterns

These patterns are frequently used in the codebase and should be followed:

### Reset Pattern

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) begin
    // Initialize signals
    counter <= '0;
    state   <= IDLE;
  end else begin
    // Regular operation
    counter <= counter_next;
    state   <= state_next;
  end
end
```

### Valid-Ready Handshake

```systemverilog
// Combinational logic
always_comb begin
  out_valid = data_available && !output_blocked;
  in_ready  = !fifo_full && !output_blocked;
end

// Transfer data on handshake
always_ff @(posedge clk) begin
  if (out_valid && out_ready) begin
    // Process data transfer
  end
end
```

### Unused Signal Handling

Use the `SVC_UNUSED` macro for signals that are intentionally unused:

```systemverilog
`SVC_UNUSED({signal1, signal2, signal3});
```

SVC_UNUSED is defined in svc_unused.sv.

## Example Code

Refer to these files as reference implementations:

- Basic module: `rtl/fifo/svc_sync_fifo.sv`
- AXI interface: `rtl/axi/svc_axi_arbiter.sv`
- Graphics module: `rtl/gfx/svc_gfx_vga.sv`
- Testbench: `tb/fifo/svc_sync_fifo_tb.sv`

## Build and Verification Commands

```bash
# Format code to match style guidelines
make format

# Lint code for style and errors
make lint

# Run all testbenches
make tb

# Run formal verification
make formal

# Run specific testbench
make <module_name>_tb

# Run specific formal verification
make <module_name>_f
```

Always run `make format` and `make lint` before committing any changes to ensure
style consistency.
