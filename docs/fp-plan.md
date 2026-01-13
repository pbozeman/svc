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

### Phase 1: Foundation

1. Add FP opcodes/constants to `svc_rv_defs.svh`
2. Create `svc_rv_fp_regfile.sv` + testbench
3. Create `svc_rv_fp_csr.sv` + testbench
4. Create `svc_rv_fp_idec.sv` + testbench
5. Add `EXT_F` parameter to `svc_rv.sv`

### Phase 2: FPU Core Integration

1. Add fpnew as git submodule (with common_cells dependency)
2. Create `svc_rv_ext_fp_ex.sv` wrapper
3. Test basic operations (FADD, FSUB, FMUL)
4. Add multi-cycle control for FDIV, FSQRT

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
fpnew (submodule) <- common_cells (submodule)
                  <- fpu_div_sqrt_mvp (optional, for DIVSQRT)

svc_rv_fp_regfile.sv  \
svc_rv_fp_csr.sv       > svc_rv_ext_fp_ex.sv -> svc_rv_stage_ex.sv
svc_rv_fp_idec.sv     /
```

## Critical Files

- `svc/rtl/rv/svc_rv_stage_ex.sv` - Core FPU integration
- `svc/rtl/rv/svc_rv_defs.svh` - All new constants
- `svc/rtl/rv/svc_rv_idec.sv` - Extend for FP opcodes
- `svc/rtl/rv/svc_rv_hazard.sv` - FP hazard integration
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
