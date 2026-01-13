# CVFPU (fpnew) Integration for RV32F Extension

## Overview

Integrate OpenHW Group CVFPU (fpnew) into the existing 5-stage pipelined RISC-V
RV32I processor to add full RV32F (single-precision floating-point) support.

**Requirements:**

- RV32F extension (single-precision, 32-bit)
- Full compliance including FDIV/FSQRT
- Target FPGA (Vivado) with DSP optimization

## Architecture Decisions

1. **Separate FP Register File**: 32-entry f0-f31, all writable (unlike x0)
2. **FP CSRs**: fcsr (frm + fflags) with read/write support
3. **Multi-cycle Operations**: FDIV/FSQRT use existing `op_active_ex` stall
   mechanism
4. **Result Source Extension**: Add `RES_FP = 3'b110` to res_src enumeration
5. **Memory Sharing**: FLW/FSW share existing data memory interface

## New Modules to Create

| Module                 | Purpose                                     |
| ---------------------- | ------------------------------------------- |
| `svc_rv_fp_regfile.sv` | 32-entry FP register file (3 read, 1 write) |
| `svc_rv_fp_csr.sv`     | FP CSRs (fflags, frm, fcsr)                 |
| `svc_rv_fp_idec.sv`    | FP instruction decoder                      |
| `svc_rv_ext_fp_ex.sv`  | fpnew wrapper for EX stage                  |
| `svc_rv_fp_hazard.sv`  | FP hazard detection                         |
| `svc_rv_fp_fwd_ex.sv`  | FP data forwarding                          |

## Existing Modules to Modify

| Module                | Changes                                        |
| --------------------- | ---------------------------------------------- |
| `svc_rv_defs.svh`     | Add FP opcodes, `RES_FP`, FP CSR addresses     |
| `svc_rv.sv`           | Add `EXT_F` parameter, instantiate FP modules  |
| `svc_rv_idec.sv`      | Recognize FLW/FSW, route to FP decoder         |
| `svc_rv_stage_id.sv`  | Instantiate FP regfile and decoder             |
| `svc_rv_stage_ex.sv`  | Instantiate FPU wrapper, integrate multi-cycle |
| `svc_rv_stage_mem.sv` | Pass FP result, handle FLW/FSW                 |
| `svc_rv_stage_wb.sv`  | Extend result mux to 7 inputs                  |
| `svc_rv_hazard.sv`    | Integrate FP hazard detection                  |
| `svc_rv_csr.sv`       | Add FP CSR routing                             |

## RV32F Instructions to Support

**Arithmetic:** FADD.S, FSUB.S, FMUL.S, FDIV.S, FSQRT.S **FMA:** FMADD.S,
FMSUB.S, FNMADD.S, FNMSUB.S **Compare:** FEQ.S, FLT.S, FLE.S, FMIN.S, FMAX.S
**Convert:** FCVT.W.S, FCVT.WU.S, FCVT.S.W, FCVT.S.WU **Move:** FMV.X.W,
FMV.W.X, FSGNJ[N/X].S **Other:** FCLASS.S, FLW, FSW

## fpnew Configuration

```systemverilog
localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
    Width:         32,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b0,
    FpFmtMask:     5'b00001,  // FP32 only
    IntFmtMask:    4'b0001    // INT32 only
};
```

## Implementation Phases

### Phase 1: Foundation ✅ COMPLETE

1. ✅ Add FP opcodes/constants to `svc_rv_defs.svh`
2. ✅ Create `svc_rv_fp_regfile.sv` + testbench (7 tests)
3. ✅ Create `svc_rv_fp_csr.sv` + testbench (10 tests)
4. ✅ Create `svc_rv_fp_idec.sv` + testbench (21 tests)
5. ✅ Add `EXT_F` parameter to `svc_rv.sv`, `svc_rv_stage_id.sv`,
   `svc_rv_stage_ex.sv`

---

## Phase 1 Detailed Specification

### 1.1 Constants to Add (`svc_rv_defs.svh`)

```systemverilog
// RV32F Opcodes
localparam logic [6:0] OP_LOAD_FP  = 7'b0000111;  // FLW
localparam logic [6:0] OP_STORE_FP = 7'b0100111;  // FSW
localparam logic [6:0] OP_FMADD    = 7'b1000011;  // FMADD.S
localparam logic [6:0] OP_FMSUB    = 7'b1000111;  // FMSUB.S
localparam logic [6:0] OP_FNMSUB   = 7'b1001011;  // FNMSUB.S
localparam logic [6:0] OP_FNMADD   = 7'b1001111;  // FNMADD.S
localparam logic [6:0] OP_FP       = 7'b1010011;  // FP arithmetic

// Extended res_src (add to existing)
localparam logic [2:0] RES_FP = 3'b110;

// FP CSR addresses
localparam logic [11:0] CSR_FFLAGS = 12'h001;
localparam logic [11:0] CSR_FRM    = 12'h002;
localparam logic [11:0] CSR_FCSR   = 12'h003;

// Rounding modes (for frm CSR and instruction rm field)
localparam logic [2:0] FRM_RNE = 3'b000;  // Round to Nearest, ties to Even
localparam logic [2:0] FRM_RTZ = 3'b001;  // Round towards Zero
localparam logic [2:0] FRM_RDN = 3'b010;  // Round Down (-inf)
localparam logic [2:0] FRM_RUP = 3'b011;  // Round Up (+inf)
localparam logic [2:0] FRM_RMM = 3'b100;  // Round to Nearest, ties to Max Magnitude
localparam logic [2:0] FRM_DYN = 3'b111;  // Dynamic (use frm CSR)

// FP funct7 values for OP_FP instructions
localparam logic [6:0] FP_FADD    = 7'b0000000;
localparam logic [6:0] FP_FSUB    = 7'b0000100;
localparam logic [6:0] FP_FMUL    = 7'b0001000;
localparam logic [6:0] FP_FDIV    = 7'b0001100;
localparam logic [6:0] FP_FSQRT   = 7'b0101100;
localparam logic [6:0] FP_FSGNJ   = 7'b0010000;
localparam logic [6:0] FP_FMINMAX = 7'b0010100;
localparam logic [6:0] FP_FCVTWS  = 7'b1100000;  // FCVT.W.S, FCVT.WU.S
localparam logic [6:0] FP_FMVXW   = 7'b1110000;  // FMV.X.W, FCLASS.S
localparam logic [6:0] FP_FCMP    = 7'b1010000;  // FEQ, FLT, FLE
localparam logic [6:0] FP_FCVTSW  = 7'b1101000;  // FCVT.S.W, FCVT.S.WU
localparam logic [6:0] FP_FMVWX   = 7'b1111000;  // FMV.W.X

// FP funct3 values
localparam logic [2:0] FP_FSGNJ_J  = 3'b000;  // FSGNJ.S
localparam logic [2:0] FP_FSGNJ_N  = 3'b001;  // FSGNJN.S
localparam logic [2:0] FP_FSGNJ_X  = 3'b010;  // FSGNJX.S
localparam logic [2:0] FP_FMIN     = 3'b000;  // FMIN.S
localparam logic [2:0] FP_FMAX     = 3'b001;  // FMAX.S
localparam logic [2:0] FP_FEQ      = 3'b010;  // FEQ.S
localparam logic [2:0] FP_FLT      = 3'b001;  // FLT.S
localparam logic [2:0] FP_FLE      = 3'b000;  // FLE.S
localparam logic [2:0] FP_FCLASS   = 3'b001;  // FCLASS.S (with FP_FMVXW)
localparam logic [2:0] FP_FMVXW_MV = 3'b000;  // FMV.X.W (with FP_FMVXW)
```

### 1.2 FP Register File (`svc_rv_fp_regfile.sv`)

```systemverilog
module svc_rv_fp_regfile #(
    parameter int XLEN = 32,
    parameter int FWD_REGFILE = 0
) (
    input logic clk,

    // Read port 1 (frs1)
    input  logic [     4:0] frs1_addr,
    output logic [XLEN-1:0] frs1_data,

    // Read port 2 (frs2)
    input  logic [     4:0] frs2_addr,
    output logic [XLEN-1:0] frs2_data,

    // Read port 3 (frs3 for FMA instructions)
    input  logic [     4:0] frs3_addr,
    output logic [XLEN-1:0] frs3_data,

    // Write port (frd)
    input logic            frd_en,
    input logic [     4:0] frd_addr,
    input logic [XLEN-1:0] frd_data
);
```

**Key differences from integer regfile:**

- All 32 registers writable (f0 is NOT hardwired to zero)
- Three read ports instead of two (for FMA rs3 operand)
- Same optional internal forwarding mechanism

### 1.3 FP CSR Module (`svc_rv_fp_csr.sv`)

```systemverilog
module svc_rv_fp_csr (
    input logic clk,
    input logic rst_n,

    // CSR interface (directly wired, not through main CSR)
    input  logic [11:0] csr_addr,
    input  logic [ 2:0] csr_op,      // funct3: CSRRW/S/C/WI/SI/CI
    input  logic [31:0] csr_wdata,   // Write data (rs1 or zimm)
    output logic [31:0] csr_rdata,
    output logic        csr_hit,     // Address matches FP CSR

    // Dynamic rounding mode output (to FPU)
    output logic [2:0] frm,

    // Exception flag accumulation (from FPU)
    input logic        fflags_set_en,
    input logic [4:0]  fflags_set    // {NV, DZ, OF, UF, NX}
);
```

**CSR Layout:**

```
fflags (0x001): [4:0] = {NV, DZ, OF, UF, NX}
frm    (0x002): [2:0] = rounding mode
fcsr   (0x003): [7:5] = frm, [4:0] = fflags
```

**CSR Operations:**

- CSRRW: Write csr_wdata, return old value
- CSRRS: Set bits from csr_wdata, return old value
- CSRRC: Clear bits from csr_wdata, return old value
- CSRRWI/SI/CI: Same but csr_wdata = zero-extended zimm[4:0]

**Flag Accumulation:**

- fflags are sticky (set via OR, never auto-cleared)
- Only cleared by explicit CSR write

### 1.4 FP Instruction Decoder (`svc_rv_fp_idec.sv`)

```systemverilog
module svc_rv_fp_idec #(
    parameter int XLEN = 32
) (
    input logic [31:0] instr,

    // Instruction classification
    output logic       is_fp,           // Any FP instruction
    output logic       is_fp_load,      // FLW
    output logic       is_fp_store,     // FSW
    output logic       is_fp_compute,   // Arithmetic/FMA/compare/convert
    output logic       is_fp_mc,        // Multi-cycle (FDIV, FSQRT)

    // Register destinations
    output logic       fp_reg_write,    // Write to FP register file
    output logic       int_reg_write,   // Write to integer register file

    // FP register indices
    output logic [4:0] frs1,
    output logic [4:0] frs2,
    output logic [4:0] frs3,           // For FMA (instr[31:27])
    output logic [4:0] frd,

    // Register usage (for hazard detection)
    output logic       frs1_used,
    output logic       frs2_used,
    output logic       frs3_used,
    output logic       int_rs1_used,   // Integer rs1 (FSW addr, FMV.W.X, FCVT.S.W)

    // FPU control (for fpnew)
    output logic [3:0] fp_op,          // fpnew operation_e
    output logic       fp_op_mod,      // Operation modifier
    output logic [2:0] fp_rm,          // Rounding mode from instruction
    output logic       fp_rm_dyn,      // Use dynamic rounding mode (frm CSR)

    // Invalid instruction
    output logic       fp_instr_invalid
);
```

**Instruction Decode Table:**

| Instruction | Opcode   | funct7  | funct3 | frs1 | frs2 | frs3 | int_rs1 | frd | int_rd |
| ----------- | -------- | ------- | ------ | ---- | ---- | ---- | ------- | --- | ------ |
| FLW         | LOAD_FP  | -       | 010    | -    | -    | -    | Y       | Y   | -      |
| FSW         | STORE_FP | -       | 010    | -    | Y    | -    | Y       | -   | -      |
| FMADD.S     | FMADD    | rs3\|00 | rm     | Y    | Y    | Y    | -       | Y   | -      |
| FMSUB.S     | FMSUB    | rs3\|00 | rm     | Y    | Y    | Y    | -       | Y   | -      |
| FNMSUB.S    | FNMSUB   | rs3\|00 | rm     | Y    | Y    | Y    | -       | Y   | -      |
| FNMADD.S    | FNMADD   | rs3\|00 | rm     | Y    | Y    | Y    | -       | Y   | -      |
| FADD.S      | FP       | 0000000 | rm     | Y    | Y    | -    | -       | Y   | -      |
| FSUB.S      | FP       | 0000100 | rm     | Y    | Y    | -    | -       | Y   | -      |
| FMUL.S      | FP       | 0001000 | rm     | Y    | Y    | -    | -       | Y   | -      |
| FDIV.S      | FP       | 0001100 | rm     | Y    | Y    | -    | -       | Y   | -      |
| FSQRT.S     | FP       | 0101100 | rm     | Y    | -    | -    | -       | Y   | -      |
| FSGNJ.S     | FP       | 0010000 | 000    | Y    | Y    | -    | -       | Y   | -      |
| FSGNJN.S    | FP       | 0010000 | 001    | Y    | Y    | -    | -       | Y   | -      |
| FSGNJX.S    | FP       | 0010000 | 010    | Y    | Y    | -    | -       | Y   | -      |
| FMIN.S      | FP       | 0010100 | 000    | Y    | Y    | -    | -       | Y   | -      |
| FMAX.S      | FP       | 0010100 | 001    | Y    | Y    | -    | -       | Y   | -      |
| FCVT.W.S    | FP       | 1100000 | rm     | Y    | -    | -    | -       | -   | Y      |
| FCVT.WU.S   | FP       | 1100000 | rm     | Y    | -    | -    | -       | -   | Y      |
| FMV.X.W     | FP       | 1110000 | 000    | Y    | -    | -    | -       | -   | Y      |
| FCLASS.S    | FP       | 1110000 | 001    | Y    | -    | -    | -       | -   | Y      |
| FEQ.S       | FP       | 1010000 | 010    | Y    | Y    | -    | -       | -   | Y      |
| FLT.S       | FP       | 1010000 | 001    | Y    | Y    | -    | -       | -   | Y      |
| FLE.S       | FP       | 1010000 | 000    | Y    | Y    | -    | -       | -   | Y      |
| FCVT.S.W    | FP       | 1101000 | rm     | -    | -    | -    | Y       | Y   | -      |
| FCVT.S.WU   | FP       | 1101000 | rm     | -    | -    | -    | Y       | Y   | -      |
| FMV.W.X     | FP       | 1111000 | 000    | -    | -    | -    | Y       | Y   | -      |

**Notes:**

- rs2[4] distinguishes signed/unsigned for FCVT: 0=signed, 1=unsigned
- fmt field (instr[26:25]) must be 00 for single-precision
- frs3 is extracted from instr[31:27] for FMA instructions

### 1.5 EXT_F Parameter (`svc_rv.sv`)

Add parameter and validation:

```systemverilog
parameter int EXT_F = 0,  // RV32F extension

// Parameter validation
if ((EXT_F == 1) && (PIPELINED == 0)) begin
  $fatal(1, "EXT_F=1 requires PIPELINED=1");
end
```

### 1.6 Testbench Strategy

**`svc_rv_fp_regfile_tb.sv`:**

- Test all 32 registers read/write (including f0)
- Test simultaneous reads from all 3 ports
- Test forwarding (if FWD_REGFILE=1)
- Test write-then-read same cycle

**`svc_rv_fp_csr_tb.sv`:**

- Test fflags read/write via all CSR ops
- Test frm read/write
- Test fcsr combined access
- Test flag accumulation (OR behavior)
- Test frm output to FPU

**`svc_rv_fp_idec_tb.sv`:**

- Test decode of all 26 RV32F instructions
- Test register usage flags for each instruction type
- Test rounding mode extraction (static vs dynamic)
- Test invalid instruction detection (wrong fmt, reserved encodings)

### Phase 2: FPU Core Integration ✅ COMPLETE

1. ✅ Set up external dependencies (fpnew submodule, common_cells)
2. ✅ Create `svc_rv_ext_fp_ex.sv` FPU wrapper module
3. ✅ Create verilator testbench `svc_rv_ext_fp_ex_tbv.sv`
4. ✅ Update Makefile include paths for external deps

### Phase 3: Pipeline Integration

1. Modify `svc_rv_stage_id.sv` - FP decode and regfile read
2. Modify `svc_rv_stage_ex.sv` - FPU instance
3. Modify `svc_rv_stage_mem.sv` - FP data path
4. Modify `svc_rv_stage_wb.sv` - FP result mux, regfile write

### Phase 4: Memory Operations

1. Extend decoder for FLW/FSW
2. Wire FP source data for FSW
3. Route load data to FP regfile for FLW

### Phase 5: Hazards and Forwarding

1. Create `svc_rv_fp_hazard.sv`
2. Create `svc_rv_fp_fwd_ex.sv`
3. Integrate with existing hazard unit
4. Handle cross-file hazards (INT<->FP)

### Phase 6: CSR and Testing

1. Wire FP CSR to CSR interface
2. Connect frm to FPU, accumulate fflags
3. Create test programs (`-march=rv32imf`)
4. Run riscv-tests F extension suite

## Key Dependencies

```
svc/external/
├── fpnew/          (submodule: openhwgroup/cvfpu)
│   └── vendor/opene906/  (integrated DIVSQRT unit)
└── common_cells/   (fetched via script, 4 files only)
    ├── lzc.sv
    ├── rr_arb_tree.sv
    ├── cf_math_pkg.sv
    └── assertions.svh

Phase 1 modules (COMPLETE):
  svc_rv_fp_regfile.sv  \
  svc_rv_fp_csr.sv       > Phase 2 (COMPLETE): svc_rv_ext_fp_ex.sv
  svc_rv_fp_idec.sv     /

Phase 3 (NEXT): Pipeline integration -> svc_rv_stage_*.sv
```

## Critical Files

**Phase 1 (Complete):**

- `svc/rtl/rv/svc_rv_defs.svh` - FP opcodes, CSR addresses, rounding modes
- `svc/rtl/rv/svc_rv_fp_regfile.sv` - 32-entry FP register file
- `svc/rtl/rv/svc_rv_fp_csr.sv` - fflags, frm, fcsr CSRs
- `svc/rtl/rv/svc_rv_fp_idec.sv` - FP instruction decoder

**Phase 2 (Complete):**

- `svc/external/fetch_common_cells.sh` - Dependency fetch script
- `svc/external/fpnew/` - FPU submodule
- `svc/external/common_cells/` - Fetched utility modules
- `svc/rtl/rv/svc_rv_ext_fp_ex.sv` - fpnew wrapper
- `svc/tb/rv/svc_rv_ext_fp_ex_tbv.sv` - FPU wrapper testbench (verilator)

**Phase 3 (Next):**

- `svc/rtl/rv/svc_rv_stage_id.sv` - FP decode and regfile read
- `svc/rtl/rv/svc_rv_stage_ex.sv` - FPU instance integration
- `svc/rtl/rv/svc_rv_stage_mem.sv` - FP data path
- `svc/rtl/rv/svc_rv_stage_wb.sv` - FP result mux, regfile write

**Reference (existing patterns):**

- `svc/rtl/rv/svc_rv_ext_div.sv` - Pattern for multi-cycle ops

## Resource Estimates (Artix-7)

- FP Regfile: ~64 LUTs
- FP CSRs: ~30 LUTs
- fpnew core: ~2000-3000 LUTs + 3-6 DSPs
- Control logic: ~200-400 LUTs
- **Total: ~2500-3500 LUTs + 3-6 DSPs**

## Risk Mitigation

| Risk              | Mitigation                                        |
| ----------------- | ------------------------------------------------- |
| Timing            | Use fpnew pipeline registers if needed            |
| Area              | Start with minimal config (FP32 only, no vectors) |
| IEEE compliance   | Leverage fpnew's proven compliance                |
| Hazard complexity | Incremental integration with extensive testing    |
