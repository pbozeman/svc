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

#### 3a. ID Stage Modifications (`svc_rv_stage_id.sv`)

**New Signals (outputs to EX):**

```systemverilog
// FP instruction classification
output logic       is_fp_ex,         // Any FP instruction
output logic       is_fp_load_ex,    // FLW
output logic       is_fp_store_ex,   // FSW
output logic       is_fp_compute_ex, // FP arithmetic
output logic       is_fp_mc_ex,      // Multi-cycle FP (FDIV/FSQRT)
output logic       fp_reg_write_ex,  // Write to FP regfile
output logic       fp_int_reg_write_ex, // FP instr writes INT regfile

// FP register data (3 read ports)
output logic [XLEN-1:0] frs1_data_ex,
output logic [XLEN-1:0] frs2_data_ex,
output logic [XLEN-1:0] frs3_data_ex,

// FP register indices (for hazard detection)
output logic [4:0] frs1_ex,
output logic [4:0] frs2_ex,
output logic [4:0] frs3_ex,
output logic [4:0] frd_ex,

// FP register usage flags (for hazard detection)
output logic       frs1_used_ex,
output logic       frs2_used_ex,
output logic       frs3_used_ex,

// Rounding mode
output logic [2:0] fp_rm_ex,
output logic       fp_rm_dyn_ex,
```

**Changes:**

1. **Instantiate FP decoder** (guarded by `EXT_F`):

   ```systemverilog
   if (EXT_F != 0) begin : g_fp_idec
     svc_rv_fp_idec fp_idec (
       .instr(instr_id),
       .is_fp(is_fp_id),
       .is_fp_load(is_fp_load_id),
       .is_fp_store(is_fp_store_id),
       .is_fp_compute(is_fp_compute_id),
       .is_fp_mc(is_fp_mc_id),
       .fp_reg_write(fp_reg_write_id),
       .int_reg_write(fp_int_reg_write_id),
       .frs1(frs1_id), .frs2(frs2_id), .frs3(frs3_id), .frd(frd_id),
       .frs1_used(frs1_used_id), .frs2_used(frs2_used_id),
       .frs3_used(frs3_used_id), .int_rs1_used(fp_int_rs1_used_id),
       .fp_rm(fp_rm_id), .fp_rm_dyn(fp_rm_dyn_id),
       .fp_instr_invalid(fp_instr_invalid_id)
     );
   end
   ```

2. **Instantiate FP register file** (guarded by `EXT_F`):

   ```systemverilog
   if (EXT_F != 0) begin : g_fp_regfile
     svc_rv_fp_regfile #(.XLEN(XLEN), .FWD_REGFILE(FWD_REGFILE)) fp_regfile (
       .clk(clk),
       .frs1_addr(frs1_id), .frs1_data(frs1_data_id),
       .frs2_addr(frs2_id), .frs2_data(frs2_data_id),
       .frs3_addr(frs3_id), .frs3_data(frs3_data_id),
       .frd_en(fp_reg_write_wb && !dmem_stall),
       .frd_addr(frd_wb),
       .frd_data(frd_data_wb)
     );
   end
   ```

3. **Update multi-cycle detection**:

   ```systemverilog
   // Extend is_mc_id to include FP multi-cycle ops
   if (EXT_F != 0) begin : g_fp_mc
     assign is_mc_id = (EXT_M != 0 && is_m_id && funct3_id[2]) || is_fp_mc_id;
   end
   ```

4. **Add FP signals to ID/EX pipeline registers**

#### 3b. EX Stage Modifications (`svc_rv_stage_ex.sv`)

**New Inputs (from ID):**

```systemverilog
input logic       is_fp_ex,
input logic       is_fp_load_ex,
input logic       is_fp_store_ex,
input logic       is_fp_compute_ex,
input logic       is_fp_mc_ex,
input logic       fp_reg_write_ex,
input logic       fp_int_reg_write_ex,
input logic [XLEN-1:0] frs1_data_ex,
input logic [XLEN-1:0] frs2_data_ex,
input logic [XLEN-1:0] frs3_data_ex,
input logic [4:0] frd_ex,
input logic [2:0] fp_rm_ex,
input logic       fp_rm_dyn_ex,
```

**New Outputs (to MEM):**

```systemverilog
output logic [XLEN-1:0] fp_result_mem,
output logic [4:0]      fflags_mem,
output logic            fp_reg_write_mem,
output logic [4:0]      frd_mem,
output logic            is_fp_load_mem,
output logic            is_fp_store_mem,
output logic [XLEN-1:0] frs2_data_mem, // For FSW store data
```

**Changes:**

1. **Instantiate FPU wrapper** (guarded by `EXT_F`):

   ```systemverilog
   if (EXT_F != 0) begin : g_fpu
     logic [2:0] frm_csr;  // From FP CSR module

     svc_rv_ext_fp_ex fpu (
       .clk(clk),
       .rst_n(rst_n),
       .op_valid(s_valid && is_fp_compute_ex && !op_active_ex),
       .instr(instr_ex),
       .frm_csr(frm_csr),
       .frs1(fwd_frs1_ex),  // Forwarded FP operands
       .frs2(fwd_frs2_ex),
       .frs3(fwd_frs3_ex),
       .rs1(fwd_rs1_ex),    // Integer source for FCVT.S.W/FMV.W.X
       .result_valid(fp_result_valid),
       .result(fp_result_ex),
       .fflags(fflags_ex),
       .busy(fp_busy_ex)
     );
   end
   ```

2. **Extend multi-cycle state machine**:

   ```systemverilog
   // m_busy_ex includes FP busy
   if (EXT_F != 0) begin : g_fp_busy
     assign m_busy_ex = div_busy || fp_busy_ex;
   end
   ```

3. **Add FP signals to EX/MEM pipeline registers**

#### 3c. MEM Stage Modifications (`svc_rv_stage_mem.sv`)

**New Inputs (from EX):**

```systemverilog
input logic [XLEN-1:0] fp_result_mem,
input logic [4:0]      fflags_mem,
input logic            fp_reg_write_mem,
input logic [4:0]      frd_mem,
input logic            is_fp_load_mem,
input logic            is_fp_store_mem,
input logic [XLEN-1:0] frs2_data_mem,
```

**New Outputs (to WB):**

```systemverilog
output logic [XLEN-1:0] fp_result_wb,
output logic [4:0]      fflags_wb,
output logic            fp_reg_write_wb,
output logic [4:0]      frd_wb,
output logic            is_fp_load_wb,
```

**Changes:**

1. **FSW store data**: Use `frs2_data_mem` instead of `rs2_data_mem` when
   `is_fp_store_mem`:

   ```systemverilog
   logic [XLEN-1:0] store_data;
   assign store_data = is_fp_store_mem ? frs2_data_mem : rs2_data_mem;
   ```

2. **FP result forwarding**: Add `fp_result_mem` to forwarding mux for FP
   hazards

3. **Pass FP signals through MEM/WB pipeline registers**

#### 3d. WB Stage Modifications (`svc_rv_stage_wb.sv`)

**New Inputs (from MEM):**

```systemverilog
input logic [XLEN-1:0] fp_result_wb,
input logic [4:0]      fflags_wb,
input logic            fp_reg_write_wb,
input logic [4:0]      frd_wb,
input logic            is_fp_load_wb,
```

**New Outputs:**

```systemverilog
// To FP regfile (in ID stage)
output logic [XLEN-1:0] frd_data_wb,
output logic [4:0]      frd_addr_wb,
output logic            frd_en_wb,

// To FP CSR (for fflags accumulation)
output logic [4:0]      fflags_set,
output logic            fflags_set_en,
```

**Changes:**

1. **Extend result mux** (add `RES_FP = 3'b110`):

   ```systemverilog
   svc_muxn #(.WIDTH(XLEN), .N(7)) mux_res (
     .sel(res_src_wb),
     .data({
       fp_result_wb,      // RES_FP (6)
       m_ext_result_wb,   // RES_M (5)
       csr_rdata_wb,      // RES_CSR (4)
       jb_tgt_wb,         // RES_TGT (3)
       pc_plus4_wb,       // RES_PC4 (2)
       ld_data_wb,        // RES_MEM (1)
       alu_result_wb      // RES_ALU (0)
     }),
     .out(rd_data_wb)
   );
   ```

2. **FP load result selection**: When `is_fp_load_wb`, route `ld_data_wb` to FP
   regfile:

   ```systemverilog
   assign frd_data_wb = is_fp_load_wb ? ld_data_wb : fp_result_wb;
   assign frd_en_wb = fp_reg_write_wb;
   assign frd_addr_wb = frd_wb;
   ```

3. **fflags accumulation**:
   ```systemverilog
   assign fflags_set = fflags_wb;
   assign fflags_set_en = fp_reg_write_wb && (|fflags_wb);
   ```

---

### Phase 4: Hazards and Forwarding

#### 4a. FP Hazard Detection (`svc_rv_fp_hazard.sv`)

**FP-specific hazards to detect:**

| Hazard Type    | Condition                           | Resolution             |
| -------------- | ----------------------------------- | ---------------------- |
| FP RAW (EX)    | frs\* matches frd in EX/MEM/WB      | Forward or stall       |
| FP Load-Use    | FLW in EX, consumer in ID           | Stall 1 cycle          |
| INT<->FP RAW   | FMV.W.X/FCVT.S.W uses INT rs1       | Use INT forwarding     |
| FP->INT RAW    | FCVT.W.S/FMV.X.W result used by INT | Forward to INT regfile |
| FP Multi-cycle | FDIV/FSQRT in progress              | Stall via op_active_ex |

**Interface:**

```systemverilog
module svc_rv_fp_hazard #(parameter int XLEN = 32) (
  // FP register usage (from ID)
  input logic [4:0] frs1_id, frs2_id, frs3_id,
  input logic       frs1_used_id, frs2_used_id, frs3_used_id,

  // FP destinations in flight
  input logic [4:0] frd_ex, frd_mem, frd_wb,
  input logic       fp_reg_write_ex, fp_reg_write_mem, fp_reg_write_wb,

  // Load detection
  input logic       is_fp_load_ex,

  // Hazard outputs
  output logic      fp_data_hazard_id,
  output logic      fp_load_hazard_id
);
```

#### 4b. FP Forwarding (`svc_rv_fp_fwd_ex.sv`)

**Forwarding paths:**

- EX→EX: From `fp_result_mem` (bypass MEM stage)
- MEM→EX: From `fp_result_wb`
- WB→ID: Internal regfile forwarding (existing `FWD_REGFILE` mechanism)

**Interface:**

```systemverilog
module svc_rv_fp_fwd_ex #(parameter int XLEN = 32) (
  // FP operands from ID
  input logic [XLEN-1:0] frs1_data_ex, frs2_data_ex, frs3_data_ex,
  input logic [4:0]      frs1_ex, frs2_ex, frs3_ex,

  // FP results from later stages
  input logic [4:0]      frd_mem, frd_wb,
  input logic            fp_reg_write_mem, fp_reg_write_wb,
  input logic [XLEN-1:0] fp_result_mem, frd_data_wb,

  // Forwarded outputs
  output logic [XLEN-1:0] fwd_frs1_ex, fwd_frs2_ex, fwd_frs3_ex
);
```

#### 4c. Integration with Existing Hazard Unit

Modify `svc_rv_hazard.sv`:

- OR `fp_data_hazard_id` with existing `data_hazard_id`
- OR `fp_load_hazard_id` with existing `load_hazard_id`
- Ensure `op_active_ex` covers FP multi-cycle ops

---

### Phase 5: FP CSR Integration

1. **Wire FP CSR module** in EX stage (or dedicated location):

   ```systemverilog
   svc_rv_fp_csr fp_csr (
     .clk(clk), .rst_n(rst_n),
     .csr_addr(imm_ex[11:0]),
     .csr_op(funct3_ex),
     .csr_wdata(rs1_data_ex),  // or zimm
     .csr_rdata(fp_csr_rdata),
     .csr_hit(fp_csr_hit),
     .frm(frm_csr),
     .fflags_set_en(fflags_set_en),
     .fflags_set(fflags_set)
   );
   ```

2. **Route CSR access**: When `csr_addr` matches FP CSRs (0x001-0x003), use
   `fp_csr_rdata` instead of main CSR

3. **Connect fflags accumulation**: Wire `fflags_set_en` and `fflags_set` from
   WB stage

---

### Phase 6: Testing

1. **Unit tests** for modified stages (extend existing testbenches)
2. **Integration test**: Simple FP program (FADD, FMUL, FLW, FSW)
3. **riscv-tests**: Run `rv32uf-p-*` tests
4. **Torture test**: Random FP instruction sequences

---

## Phase 3 Detailed Signal Flow

```
ID Stage                    EX Stage                  MEM Stage               WB Stage
=========                   =========                 ==========              =========
instr_id ──┬──> idec        instr_ex ──> fpu         fp_result_mem ──────────> fp_result_wb
           │                             │                                          │
           └──> fp_idec ───────────────> │                                          v
                    │                    v                                    result mux
                    v              fp_result_ex ──────>                            │
              fp_regfile                                                           v
              ┌───┼───┐                                                      frd_data_wb
              │   │   │                                                           │
           frs1 frs2 frs3 ────────> fwd ────────> operands                        │
                                                                                  │
                                                                                  v
              <─────────────────────────────────────────────────────────── frd_en_wb
```

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

Phase 1 (COMPLETE):
  svc_rv_fp_regfile.sv, svc_rv_fp_csr.sv, svc_rv_fp_idec.sv

Phase 2 (COMPLETE):
  svc_rv_ext_fp_ex.sv (fpnew wrapper)

Phase 3 (NEXT):
  svc_rv_stage_id.sv, svc_rv_stage_ex.sv, svc_rv_stage_mem.sv, svc_rv_stage_wb.sv

Phase 4:
  svc_rv_fp_hazard.sv, svc_rv_fp_fwd_ex.sv, svc_rv_hazard.sv (modify)

Phase 5:
  FP CSR integration

Phase 6:
  Testing (rv32uf-p-* tests)
```

## Critical Files

**Phase 1 (Complete):**

- `rtl/rv/svc_rv_defs.svh` - FP opcodes, CSR addresses, rounding modes
- `rtl/rv/svc_rv_fp_regfile.sv` - 32-entry FP register file
- `rtl/rv/svc_rv_fp_csr.sv` - fflags, frm, fcsr CSRs
- `rtl/rv/svc_rv_fp_idec.sv` - FP instruction decoder

**Phase 2 (Complete):**

- `external/fetch_common_cells.sh` - Dependency fetch script
- `external/fpnew/` - FPU submodule
- `external/common_cells/` - Fetched utility modules
- `rtl/rv/svc_rv_ext_fp_ex.sv` - fpnew wrapper
- `tb/rv/svc_rv_ext_fp_ex_tbv.sv` - FPU wrapper testbench (verilator)

**Phase 3 (Next):**

- `rtl/rv/svc_rv_stage_id.sv` - FP decode, regfile read, ID/EX pipe
- `rtl/rv/svc_rv_stage_ex.sv` - FPU instance, multi-cycle control
- `rtl/rv/svc_rv_stage_mem.sv` - FP data path, FSW store data
- `rtl/rv/svc_rv_stage_wb.sv` - FP result mux (7-way), FP regfile write

**Phase 4:**

- `rtl/rv/svc_rv_fp_hazard.sv` - FP hazard detection (new)
- `rtl/rv/svc_rv_fp_fwd_ex.sv` - FP forwarding (new)
- `rtl/rv/svc_rv_hazard.sv` - Integrate FP hazards (modify)

**Reference (existing patterns):**

- `rtl/rv/svc_rv_ext_div.sv` - Pattern for multi-cycle ops
- `rtl/rv/svc_rv_fwd_ex.sv` - Pattern for forwarding
- `rtl/rv/svc_rv_hazard.sv` - Pattern for hazard detection

## FPU Latency Configuration

fpnew's `PipeRegs` parameter controls internal pipeline registers, separate from
our CPU stage registers. This is tunable for timing closure.

**Current configuration** (`svc_rv_ext_fp_ex.sv`):

```systemverilog
PipeRegs: '{default: 0}  // Combinational - result same cycle
```

**Operation latencies with PipeRegs=0:**

| Operation                     | Cycles | Notes                         |
| ----------------------------- | ------ | ----------------------------- |
| FADD, FSUB, FMUL, FMADD, etc. | 1      | Combinational through fpnew   |
| FMIN, FMAX, FSGNJ, FCMP       | 1      | NONCOMP unit, simple logic    |
| FCVT, FCLASS                  | 1      | CONV unit                     |
| FMV.X.W, FMV.W.X              | 1      | Bypasses fpnew entirely       |
| FDIV, FSQRT                   | ~28    | T-Head E906 iterative divider |

**If EX stage timing fails**, increase PipeRegs:

```systemverilog
PipeRegs: '{
    '{default: 1},  // ADDMUL: +1 cycle (FADD/FMUL/FMADD become 2-cycle)
    '{default: 0},  // DIVSQRT: already multi-cycle
    '{default: 0},  // NONCOMP: keep combinational (simple ops)
    '{default: 0}   // CONV: keep combinational
}
```

With PipeRegs=1 for ADDMUL, FADD/FMUL/FMADD become 2-cycle operations. The
existing `op_active_ex` stall mechanism (used for FDIV/FSQRT) handles this
automatically - no architectural changes needed, just a config tweak.

**FP Forwarding considerations:**

FP forwarding should be controlled separately from integer forwarding because:

1. With `PipeRegs=0`: FP result available in EX, can forward EX→EX (like INT)
2. With `PipeRegs=1`: FP result available in MEM, cannot forward EX→EX (must
   stall)

Add parameter to control this:

```systemverilog
parameter int FWD_FP = 1  // 0=stall on FP RAW, 1=forward FP results
```

When `PipeRegs > 0`, set `FWD_FP = 0` to force stalls instead of attempting
impossible forwarding. The hazard unit must account for this:

```systemverilog
// FP hazard with forwarding disabled - must stall
assign fp_data_hazard_id = (FWD_FP == 0) ?
    (frs_matches_frd_ex || frs_matches_frd_mem) :  // Stall for EX and MEM
    (is_fp_load_ex && frs_matches_frd_ex);         // Only load-use stall
```

**Recommendation**: Start with PipeRegs=0, check timing after synthesis. If EX
stage is critical path, bump ADDMUL to 1. FPGA DSP slices are fast, so
combinational may work.

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
