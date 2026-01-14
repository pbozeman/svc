`ifndef SVC_RV_FP_IDEC_SV
`define SVC_RV_FP_IDEC_SV

`include "svc.sv"

//
// RISC-V Floating-Point Instruction Decoder
//
// Decodes RV32F instructions and generates control signals for the FPU.
// Supports: FLW, FSW, FMA variants, arithmetic, compare, convert, move.
//
module svc_rv_fp_idec #(
    // verilator lint_off UNUSEDPARAM
    parameter int XLEN = 32  // Reserved for RV64/D extension
    // verilator lint_on UNUSEDPARAM
) (
    input logic [31:0] instr,

    //
    // Instruction classification
    //
    output logic is_fp,          // Any FP instruction
    output logic is_fp_load,     // FLW
    output logic is_fp_store,    // FSW
    output logic is_fp_compute,  // Arithmetic/FMA/compare/convert
    output logic is_fp_mc,       // Multi-cycle (FDIV, FSQRT)

    //
    // Register destinations
    //
    output logic fp_reg_write,  // Write to FP register file
    output logic int_reg_write, // Write to integer register file

    //
    // FP register indices
    //
    output logic [4:0] fp_rs1,
    output logic [4:0] fp_rs2,
    output logic [4:0] fp_rs3,  // For FMA (instr[31:27])
    output logic [4:0] fp_rd,

    //
    // Register usage (for hazard detection)
    //
    output logic fp_rs1_used,
    output logic fp_rs2_used,
    output logic fp_rs3_used,
    output logic int_rs1_used, // Integer rs1 (FSW addr, FMV.W.X, FCVT.S.W)

    //
    // Rounding mode
    //
    output logic [2:0] fp_rm,     // Rounding mode from instruction
    output logic       fp_rm_dyn, // Use dynamic rounding mode (frm CSR)

    //
    // Invalid instruction
    //
    output logic fp_instr_invalid
);

  `include "svc_rv_defs.svh"

  //
  // Instruction field extraction
  //
  logic [6:0] opcode;
  logic [4:0] rd;
  logic [4:0] rs1;
  logic [4:0] rs2;
  logic [2:0] funct3;
  logic [6:0] funct7;
  logic [1:0] fmt;
  logic [4:0] rs3;

  assign opcode    = instr[6:0];
  assign rd        = instr[11:7];
  assign funct3    = instr[14:12];
  assign rs1       = instr[19:15];
  assign rs2       = instr[24:20];
  assign funct7    = instr[31:25];
  assign fmt       = instr[26:25];
  assign rs3       = instr[31:27];

  //
  // FP register indices
  //
  assign fp_rs1    = rs1;
  assign fp_rs2    = rs2;
  assign fp_rs3    = rs3;
  assign fp_rd     = rd;

  //
  // Rounding mode extraction
  //
  assign fp_rm     = funct3;
  assign fp_rm_dyn = (funct3 == FRM_DYN);

  //
  // Opcode detection
  //
  logic op_load_fp;
  logic op_store_fp;
  logic op_fmadd;
  logic op_fmsub;
  logic op_fnmsub;
  logic op_fnmadd;
  logic op_fp;

  assign op_load_fp  = (opcode == OP_LOAD_FP);
  assign op_store_fp = (opcode == OP_STORE_FP);
  assign op_fmadd    = (opcode == OP_FMADD);
  assign op_fmsub    = (opcode == OP_FMSUB);
  assign op_fnmsub   = (opcode == OP_FNMSUB);
  assign op_fnmadd   = (opcode == OP_FNMADD);
  assign op_fp       = (opcode == OP_FP);

  //
  // FMA group detection
  //
  logic is_fma;
  assign is_fma = op_fmadd || op_fmsub || op_fnmsub || op_fnmadd;

  //
  // OP_FP funct7 detection
  //
  logic is_fadd, is_fsub, is_fmul, is_fdiv, is_fsqrt;
  logic is_fsgnj, is_fminmax, is_fcvtws, is_fmvxw, is_fcmp;
  logic is_fcvtsw, is_fmvwx;

  assign is_fadd = op_fp && (funct7 == FP7_FADD);
  assign is_fsub = op_fp && (funct7 == FP7_FSUB);
  assign is_fmul = op_fp && (funct7 == FP7_FMUL);
  assign is_fdiv = op_fp && (funct7 == FP7_FDIV);
  assign is_fsqrt = op_fp && (funct7 == FP7_FSQRT);
  assign is_fsgnj = op_fp && (funct7 == FP7_FSGNJ);
  assign is_fminmax = op_fp && (funct7 == FP7_FMINMAX);
  assign is_fcvtws = op_fp && (funct7 == FP7_FCVTWS);
  assign is_fmvxw = op_fp && (funct7 == FP7_FMVXW);
  assign is_fcmp = op_fp && (funct7 == FP7_FCMP);
  assign is_fcvtsw = op_fp && (funct7 == FP7_FCVTSW);
  assign is_fmvwx = op_fp && (funct7 == FP7_FMVWX);

  //
  // Instruction classification outputs
  //
  // Note: is_fp is true for ANY FP opcode (for exception handling),
  // while is_fp_load/store require valid funct3 for execution control.
  //
  assign is_fp_load = op_load_fp && (funct3 == 3'b010);  // FLW
  assign is_fp_store = op_store_fp && (funct3 == 3'b010);  // FSW
  assign is_fp_compute = is_fma || op_fp;
  assign is_fp_mc = is_fdiv || is_fsqrt;
  assign is_fp = op_load_fp || op_store_fp || is_fma || op_fp;

  //
  // Register write destinations
  //
  // Instructions that write to FP register file:
  // - FLW, FMA variants, FADD, FSUB, FMUL, FDIV, FSQRT
  // - FSGNJ variants, FMIN/FMAX, FCVT.S.W, FCVT.S.WU, FMV.W.X
  //
  // Instructions that write to integer register file:
  // - FCVT.W.S, FCVT.WU.S, FMV.X.W, FCLASS.S, FEQ/FLT/FLE
  //
  assign fp_reg_write = (is_fp_load || is_fma || is_fadd || is_fsub ||
                         is_fmul || is_fdiv || is_fsqrt || is_fsgnj ||
                         is_fminmax || is_fcvtsw || is_fmvwx);

  assign int_reg_write = (is_fcvtws || is_fmvxw || is_fcmp);

  //
  // Register usage for hazard detection
  //
  // fp_rs1_used: Most FP compute instructions use fp_rs1
  //   - NOT used by: FCVT.S.W, FCVT.S.WU, FMV.W.X (use int rs1)
  //
  // fp_rs2_used: Two-operand FP instructions
  //   - FMA (rs2), FADD, FSUB, FMUL, FDIV, FSGNJ, FMINMAX, FCMP, FSW
  //
  // fp_rs3_used: Only FMA instructions use rs3
  //
  // int_rs1_used: Integer rs1 as address or source
  //   - FLW, FSW (base address), FCVT.S.W, FCVT.S.WU, FMV.W.X
  //
  assign fp_rs1_used = (is_fma || is_fadd || is_fsub || is_fmul || is_fdiv ||
                        is_fsqrt || is_fsgnj || is_fminmax || is_fcvtws ||
                        is_fmvxw || is_fcmp);

  assign fp_rs2_used = (is_fma || is_fadd || is_fsub || is_fmul || is_fdiv ||
                        is_fsgnj || is_fminmax || is_fcmp || is_fp_store);

  assign fp_rs3_used = is_fma;

  assign int_rs1_used = (is_fp_load || is_fp_store || is_fcvtsw || is_fmvwx);

  //
  // Invalid instruction detection
  //
  // Invalid if:
  // - fmt != 00 for single-precision (bits [26:25])
  // - Unknown funct7 for OP_FP
  // - Wrong funct3 for FLW/FSW
  // - Reserved rs2 encoding for FCVT/FSQRT
  //
  logic invalid_fmt;
  logic invalid_funct7;
  logic invalid_load_store;
  logic invalid_fcvt_rs2;
  logic invalid_fsqrt_rs2;
  logic invalid_fmv_funct3;

  // Format must be 00 for single-precision
  assign invalid_fmt = is_fp_compute && (fmt != 2'b00);

  // Unknown funct7 for OP_FP
  assign invalid_funct7 = op_fp &&
      !(is_fadd || is_fsub || is_fmul || is_fdiv || is_fsqrt || is_fsgnj ||
        is_fminmax || is_fcvtws || is_fmvxw || is_fcmp || is_fcvtsw || is_fmvwx)
      ;

  // FLW/FSW must have funct3 = 010
  assign
      invalid_load_store = ((op_load_fp || op_store_fp) && (funct3 != 3'b010));

  // FCVT.W.S/WU.S: rs2[4:1] must be 0 (rs2[0] selects signed/unsigned)
  // FCVT.S.W/WU: rs2[4:1] must be 0
  assign invalid_fcvt_rs2 = ((is_fcvtws || is_fcvtsw) && (rs2[4:1] != 4'b0));

  // FSQRT: rs2 must be 0
  assign invalid_fsqrt_rs2 = is_fsqrt && (rs2 != 5'b0);

  // FMV.X.W/FMV.W.X/FCLASS: funct3 must be valid
  assign invalid_fmv_funct3 = (is_fmvxw && (funct3 != FP3_FMV) &&
                               (funct3 != FP3_FCLASS)) ||
      (is_fmvwx && (funct3 != FP3_FMV));

  assign fp_instr_invalid = is_fp &&
      (invalid_fmt || invalid_funct7 || invalid_load_store ||
       invalid_fcvt_rs2 || invalid_fsqrt_rs2 || invalid_fmv_funct3);

endmodule

`endif
