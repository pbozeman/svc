# RISC-V Processor

A configurable RISC-V RV32I processor implementation with a 5-stage pipeline
architecture.

## Overview

The RISC-V processor implements the base RV32I integer instruction set with
support for:

- **ISA**: RV32I base integer instruction set
- **Extensions**: Zicntr (base counters and timers)
- **Pipeline**: 5-stage classic RISC pipeline (IF/ID/EX/MEM/WB)
- **Configuration**: Parameterized for combinational or pipelined operation
- **Memory**: Separate instruction and data memory interfaces
- **CSR**: Control and Status Registers (CYCLE, INSTRET counters)

## Architecture

### Pipeline Stages

1. **IF (Instruction Fetch)**: Fetch instruction from memory
2. **ID (Instruction Decode)**: Decode instruction and read register file
3. **EX (Execute)**: Execute ALU operations and branch comparisons
4. **MEM (Memory)**: Access data memory for loads/stores
5. **WB (Write Back)**: Write results back to register file

### Pipeline Modes

The processor supports two operating modes controlled by the `PIPELINED`
parameter:

- **Combinational (PIPELINED=0)**: Minimal pipeline registers for smallest area
  and fastest compilation. Compatible with SRAM-style memories (combinational
  reads). Lower maximum clock frequency.

- **Pipelined (PIPELINED=1)**: Full pipeline registers between all stages for
  maximum clock frequency. Required for BRAM-style memories (registered reads).
  Includes hazard detection and data forwarding.

## Modules

### Top-Level Processor

- **svc_rv.sv** - Complete RISC-V core with configurable pipeline
  - Parameters: XLEN, IMEM_AW, DMEM_AW, PIPELINED, FWD_REGFILE, MEM_TYPE
  - Interfaces: instruction memory (read-only), data memory (read/write)
  - Architecture: Stage-based organization with dedicated modules per pipeline
    stage

### SoC Integration

- **svc_rv_soc_bram.sv** - Complete SoC with BRAM memories

  - Includes instruction and data BRAM instances
  - Configured for PIPELINED=1, MEM_TYPE=MEM_TYPE_BRAM
  - Supports initialization file for instruction memory

- **svc_rv_soc_sram.sv** - Complete SoC with SRAM memories
  - Includes instruction and data SRAM instances
  - Supports both combinational and pipelined modes
  - Zero-latency SRAM reads

### Pipeline Stage Modules

The processor pipeline is organized into dedicated stage modules that
encapsulate all logic for each pipeline stage:

- **svc_rv_stage_if.sv** - Instruction Fetch stage

  - PC management and generation
  - Instruction memory interface
  - Memory-type specific fetch adapters (SRAM/BRAM)
  - IF/ID pipeline register
  - Branch prediction target input

- **svc_rv_stage_id.sv** - Instruction Decode stage

  - Instruction decoder (instantiates svc_rv_idec.sv)
  - Register file (instantiates svc_rv_regfile.sv)
  - Immediate value generation
  - Branch prediction logic (static BTFNT)
  - ID/EX pipeline register

- **svc_rv_stage_ex.sv** - Execute stage

  - ALU operations (instantiates svc_rv_alu.sv)
  - Branch comparator (instantiates svc_rv_bcmp.sv)
  - Jump/branch target calculation
  - CSR operations (instantiates svc_rv_csr.sv)
  - M extension support (instantiates svc_rv_ext_m.sv or svc_rv_ext_zmmul.sv)
  - Data forwarding (instantiates svc_rv_fwd_ex.sv)
  - Multi-cycle operation control
  - EX/MEM pipeline register

- **svc_rv_stage_mem.sv** - Memory Access stage

  - Load data formatting (instantiates svc_rv_ld_fmt.sv)
  - Store data formatting (instantiates svc_rv_st_fmt.sv)
  - Data memory interface
  - MEM/WB pipeline register

- **svc_rv_stage_wb.sv** - Write-Back stage
  - Final result selection mux
  - EBREAK detection
  - Register write-back to ID stage

### Functional Units

- **svc_rv_alu.sv** - Arithmetic Logic Unit
  - Operations: ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA
- **svc_rv_alu_dec.sv** - ALU operation decoder
- **svc_rv_bcmp.sv** - Branch comparison unit
  - Comparisons: EQ, NE, LT, GE, LTU, GEU
- **svc_rv_idec.sv** - Instruction decoder
  - Generates all control signals from instruction encoding
- **svc_rv_regfile.sv** - 32-entry register file
  - Configurable forwarding (FWD_REGFILE parameter)
  - x0 hardwired to zero
- **svc_rv_csr.sv** - Control and Status Register file
  - Implements CYCLE, CYCLEH, INSTRET, INSTRETH counters
- **svc_rv_pc.sv** - Program Counter logic

### Memory Adapters

Memory-specific instruction fetch adapters handle timing differences:

- **svc_rv_if_sram.sv** - SRAM instruction fetch adapter
  - Combinational read path for zero-latency SRAM
- **svc_rv_if_bram.sv** - BRAM instruction fetch adapter
  - Handles 1-cycle read latency of registered BRAM reads

### Data Formatting

- **svc_rv_ld_fmt.sv** - Load data formatter
  - Handles LB, LH, LW, LBU, LHU with proper alignment and sign extension
- **svc_rv_st_fmt.sv** - Store data formatter
  - Generates proper wdata and wstrb for SB, SH, SW

### Hazard Detection and Forwarding

- **svc_rv_hazard.sv** - Pipeline hazard detection unit
  - Detects data hazards between pipeline stages (RAW hazards)
  - Detects load-use hazards and branch hazards
  - Generates stall and flush signals for hazard resolution
  - Configurable forwarding mode (FWD parameter)
- **svc_rv_fwd_ex.sv** - Data forwarding unit
  - MEM→EX forwarding (EX hazard resolution)
  - WB→EX forwarding (MEM hazard resolution)
  - Forwarding priority: MEM > WB > regfile

### Header Files

- **svc_rv_defs.svh** - Shared constant definitions
  - ALU operations, instruction opcodes, control signal encodings
  - Included inside module bodies (not a package)
- **svc_rv_asm.svh** - Assembly instruction macros for testbenches
  - Macros for generating RISC-V instructions in tests

## Parameters

### Core Parameters

- **XLEN** (default: 32) - Register width (currently only 32 supported)
- **IMEM_AW** (default: 10) - Instruction memory address width in bits
- **DMEM_AW** (default: 10) - Data memory address width in bits

### Pipeline Configuration

- **PIPELINED** (default: 0) - Pipeline register enable

  - 0: Combinational mode (minimal registers)
  - 1: Pipelined mode (full pipeline registers)

- **FWD_REGFILE** (default: PIPELINED) - Register file forwarding

  - 0: No forwarding (simpler, more hazards)
  - 1: Forwarding enabled (reduces hazards)
  - Requires PIPELINED=1

- **MEM_TYPE** (default: 0) - Memory type
  - 0: MEM_TYPE_SRAM (combinational reads, 0-cycle latency)
  - 1: MEM_TYPE_BRAM (registered reads, 1-cycle latency)
  - MEM_TYPE_BRAM requires PIPELINED=1

## Memory Interfaces

### Instruction Memory (Read-Only)

```systemverilog
output logic        imem_ren,    // Read enable
output logic [31:0] imem_raddr,  // Read address (byte-aligned)
input  logic [31:0] imem_rdata   // Read data
```

### Data Memory (Read/Write)

```systemverilog
// Read interface
output logic        dmem_ren,    // Read enable
output logic [31:0] dmem_raddr,  // Read address (byte-aligned)
input  logic [31:0] dmem_rdata,  // Read data

// Write interface
output logic        dmem_we,     // Write enable
output logic [31:0] dmem_waddr,  // Write address (byte-aligned)
output logic [31:0] dmem_wdata,  // Write data
output logic [ 3:0] dmem_wstrb   // Write strobe (byte enables)
```

## Usage Examples

### Combinational Mode with SRAM

```systemverilog
svc_rv #(
    .XLEN      (32),
    .IMEM_AW   (12),           // 4KB instruction memory
    .DMEM_AW   (12),           // 4KB data memory
    .PIPELINED (0),            // Combinational mode
    .MEM_TYPE  (MEM_TYPE_SRAM) // SRAM memories
) cpu (
    .clk        (clk),
    .rst_n      (rst_n),
    .imem_ren   (imem_ren),
    .imem_raddr (imem_raddr),
    .imem_rdata (imem_rdata),
    .dmem_ren   (dmem_ren),
    .dmem_raddr (dmem_raddr),
    .dmem_rdata (dmem_rdata),
    .dmem_we    (dmem_we),
    .dmem_waddr (dmem_waddr),
    .dmem_wdata (dmem_wdata),
    .dmem_wstrb (dmem_wstrb),
    .ebreak     (ebreak)
);
```

### Pipelined Mode with BRAM

```systemverilog
svc_rv_soc_bram #(
    .XLEN        (32),
    .IMEM_AW     (10),              // 1KB instruction memory
    .DMEM_AW     (10),              // 1KB data memory
    .PIPELINED   (1),               // Fully pipelined
    .FWD_REGFILE (1),               // Enable forwarding
    .IMEM_INIT   ("program.hex")    // Initialize instruction memory
) soc (
    .clk    (clk),
    .rst_n  (rst_n),
    .ebreak (ebreak)
);
```

### High-Performance Configuration

```systemverilog
svc_rv #(
    .XLEN        (32),
    .IMEM_AW     (14),              // 16KB instruction memory
    .DMEM_AW     (14),              // 16KB data memory
    .PIPELINED   (1),               // Full pipeline
    .FWD_REGFILE (1),               // Forwarding enabled
    .MEM_TYPE    (MEM_TYPE_BRAM)    // BRAM timing
) cpu (
    // ... port connections
);
```

## Instruction Set Support

### RV32I Base Integer Instruction Set

**Arithmetic/Logic**:

- Integer operations: ADD, SUB, AND, OR, XOR, SLT, SLTU
- Immediate operations: ADDI, ANDI, ORI, XORI, SLTI, SLTIU
- Shifts: SLL, SRL, SRA, SLLI, SRLI, SRAI

**Loads/Stores**:

- Loads: LB, LH, LW, LBU, LHU
- Stores: SB, SH, SW

**Control Transfer**:

- Branches: BEQ, BNE, BLT, BGE, BLTU, BGEU
- Jumps: JAL, JALR

**Upper Immediate**:

- LUI, AUIPC

**System**:

- ECALL, EBREAK
- CSR instructions: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI

### Zicntr Extension

**Performance Counters**:

- CYCLE, CYCLEH - Cycle counter (64-bit)
- INSTRET, INSTRETH - Instructions retired counter (64-bit)

## Design Considerations

### Memory Type Selection

Choose memory type based on your target platform:

- **SRAM (MEM_TYPE_SRAM)**: Use for ASIC or FPGA with SRAM primitives

  - Combinational reads (0-cycle latency)
  - Can operate in combinational mode (PIPELINED=0) for minimal area
  - Lower maximum frequency in combinational mode

- **BRAM (MEM_TYPE_BRAM)**: Use for FPGA with block RAM primitives
  - Registered reads (1-cycle latency)
  - Requires PIPELINED=1
  - Higher maximum frequency with full pipeline
  - More efficient FPGA resource usage

### Pipeline Configuration Trade-offs

- **Combinational (PIPELINED=0)**:

  - Advantages: Smaller area, simpler design, faster compilation
  - Disadvantages: Lower clock frequency, SRAM only
  - Best for: Area-constrained designs, simple applications

- **Pipelined (PIPELINED=1)**:
  - Advantages: Higher clock frequency, supports BRAM, better throughput
  - Disadvantages: Larger area, more complex hazard handling
  - Best for: Performance-critical designs, BRAM-based memories

### Forwarding Configuration

- **No forwarding (FWD_REGFILE=0)**:

  - Simpler regfile design
  - More pipeline stalls on data hazards
  - Use when area is critical and performance is less important

- **Forwarding (FWD_REGFILE=1)**:
  - Reduces stalls by forwarding ALU results
  - Better performance on data-dependent code
  - Requires PIPELINED=1
  - Use for better performance

## Testing

The rv/ directory has comprehensive test coverage:

```bash
# Run all RISC-V tests
make svc_rv_soc_bram_tb
make svc_rv_soc_sram_tb
make svc_rv_soc_sram_pipelined_tb

# Run individual component tests
make svc_rv_alu_tb
make svc_rv_idec_tb
make svc_rv_regfile_tb
make svc_rv_hazard_tb

# Test assembly macros
make svc_rv_asm_tb
```

### SoC Test Strategy

SoC integration tests use **selective coverage** to prevent combinatorial
explosion while maintaining quality:

**Tier 1 - Baseline:**

- `svc_rv_soc_bram_tb` - Base configuration (smoke test)

**Tier 2 - Individual Features:**

- `svc_rv_soc_bram_fwd_tb` - Data forwarding
- `svc_rv_soc_bram_bpred_tb` - Branch prediction
- `svc_rv_soc_bram_zmmul_tb` - Zmmul multiply extension

**Tier 3 - Critical Interactions:**

- `svc_rv_soc_bram_zmmul_fwd_tb` - Zmmul + forwarding

This strategy tests:

- Base configuration for regression
- Each feature individually for isolation
- Most important interaction (Zmmul+forwarding for multiply result reuse)

**Policy:** Resist adding more combinations unless there is evidence of a
feature interaction bug. Most bugs are found in baseline or individual feature
tests.

See tb/rv/ for testbench implementations.

## References

- RISC-V Instruction Set Manual: <https://github.com/riscv/riscv-isa-manual>
- RV32I Base Integer Instruction Set
- Zicntr Standard Extension for Base Counters and Timers
