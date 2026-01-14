`ifndef SVC_RV_EXT_FP_EX_SV
`define SVC_RV_EXT_FP_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Floating-Point Execution Unit Wrapper
//
// Wraps fpnew_top to provide a simplified interface for the EX stage.
// Maps RISC-V RV32F instruction encodings to fpnew operation codes.
//
// Multi-cycle operations (FDIV, FSQRT) use valid/ready handshaking
// integrated with the pipeline's op_active_ex stall mechanism.
//
// NOTE: This module requires EXT_F to be defined. When EXT_F=0, a stub
// implementation is provided to avoid iverilog parsing fpnew code.
//
module svc_rv_ext_fp_ex (
    input logic clk,
    input logic rst_n,

    //
    // Operation control
    //
    input logic        op_valid,   // Start new operation
    input logic [31:0] instr,      // Full instruction for decode
    input logic [ 2:0] fp_rm,      // Rounding mode from ID stage
    input logic        fp_rm_dyn,  // Use dynamic rounding mode
    input logic [ 2:0] frm_csr,    // Dynamic rounding mode from fcsr

    //
    // Operands
    //
    input logic [31:0] fp_rs1,  // FP source 1
    input logic [31:0] fp_rs2,  // FP source 2
    input logic [31:0] fp_rs3,  // FP source 3 (FMA only)
    input logic [31:0] rs1,     // Integer source (for FCVT.S.W, FMV.W.X)

    //
    // Results
    //
    output logic        result_valid,
    output logic [31:0] result,
    output logic [ 4:0] fflags,        // Exception flags {NV, DZ, OF, UF, NX}

    //
    // Control
    //
    output logic busy  // Multi-cycle op in progress
);

`ifdef EXT_F
  // Import fpnew types (only when EXT_F is enabled)
  import fpnew_pkg::*;

  //
  // Instruction field extraction
  //
  logic [6:0] opcode;
  logic [2:0] funct3;
  logic [6:0] funct7;
  logic [4:0] rs2_field;

  assign opcode    = instr[6:0];
  assign funct3    = instr[14:12];
  assign funct7    = instr[31:25];
  assign rs2_field = instr[24:20];

  `include "svc_rv_defs.svh"

  //
  // Opcode detection
  //
  logic op_fmadd, op_fmsub, op_fnmsub, op_fnmadd, op_fp;

  assign op_fmadd  = (opcode == OP_FMADD);
  assign op_fmsub  = (opcode == OP_FMSUB);
  assign op_fnmsub = (opcode == OP_FNMSUB);
  assign op_fnmadd = (opcode == OP_FNMADD);
  assign op_fp     = (opcode == OP_FP);

  //
  // OP_FP funct7 detection
  //
  logic is_fadd, is_fsub, is_fmul, is_fdiv, is_fsqrt;
  logic is_fsgnj, is_fminmax, is_fcvtws, is_fmvxw, is_fcmp;
  logic is_fcvtsw, is_fmvwx;
  logic is_fclass;

  assign is_fadd    = op_fp && (funct7 == FP7_FADD);
  assign is_fsub    = op_fp && (funct7 == FP7_FSUB);
  assign is_fmul    = op_fp && (funct7 == FP7_FMUL);
  assign is_fdiv    = op_fp && (funct7 == FP7_FDIV);
  assign is_fsqrt   = op_fp && (funct7 == FP7_FSQRT);
  assign is_fsgnj   = op_fp && (funct7 == FP7_FSGNJ);
  assign is_fminmax = op_fp && (funct7 == FP7_FMINMAX);
  assign is_fcvtws  = op_fp && (funct7 == FP7_FCVTWS);
  assign is_fmvxw   = op_fp && (funct7 == FP7_FMVXW) && (funct3 == FP3_FMV);
  assign is_fclass  = op_fp && (funct7 == FP7_FMVXW) && (funct3 == FP3_FCLASS);
  assign is_fcmp    = op_fp && (funct7 == FP7_FCMP);
  assign is_fcvtsw  = op_fp && (funct7 == FP7_FCVTSW);
  assign is_fmvwx   = op_fp && (funct7 == FP7_FMVWX);

  //
  // Operation mapping to fpnew
  //
  // fpnew operation codes:
  //   FMADD=0, FNMSUB=1, ADD=2, MUL=3
  //   DIV=4, SQRT=5
  //   SGNJ=6, MINMAX=7, CMP=8, CLASSIFY=9
  //   F2F=10, F2I=11, I2F=12
  //
  operation_e fp_op;
  logic       fp_op_mod;
  logic       use_fpu;
  logic       is_fmv;  // FMV.X.W or FMV.W.X (bypass FPU)

  always_comb begin
    fp_op     = FMADD;
    fp_op_mod = 1'b0;
    use_fpu   = 1'b1;
    is_fmv    = 1'b0;

    if (op_fmadd) begin
      // FMADD.S: (a * b) + c
      fp_op = FMADD;
    end else if (op_fmsub) begin
      // FMSUB.S: (a * b) - c = (a * b) + (-c)
      fp_op     = FMADD;
      fp_op_mod = 1'b1;
    end else if (op_fnmsub) begin
      // FNMSUB.S: -(a * b) + c
      fp_op = FNMSUB;
    end else if (op_fnmadd) begin
      // FNMADD.S: -(a * b) - c = -(a * b) + (-c)
      fp_op     = FNMSUB;
      fp_op_mod = 1'b1;
    end else if (is_fadd) begin
      fp_op = ADD;
    end else if (is_fsub) begin
      fp_op     = ADD;
      fp_op_mod = 1'b1;
    end else if (is_fmul) begin
      fp_op = MUL;
    end else if (is_fdiv) begin
      fp_op = DIV;
    end else if (is_fsqrt) begin
      fp_op = SQRT;
    end else if (is_fsgnj) begin
      fp_op     = SGNJ;
      // op_mod encodes which sign operation:
      // 0 = FSGNJ, 1 = FSGNJN
      // FSGNJX uses funct3 directly in fpnew
      fp_op_mod = (funct3 == FP3_FSGNJN);
    end else if (is_fminmax) begin
      fp_op     = MINMAX;
      // op_mod: 0 = MIN, 1 = MAX
      fp_op_mod = (funct3 == FP3_FMAX);
    end else if (is_fcmp) begin
      fp_op = CMP;
      // op_mod encodes comparison type via funct3
    end else if (is_fclass) begin
      fp_op = CLASSIFY;
    end else if (is_fcvtws) begin
      // FCVT.W.S, FCVT.WU.S: Float to Int
      fp_op     = F2I;
      // op_mod: 0 = signed (W), 1 = unsigned (WU)
      fp_op_mod = rs2_field[0];
    end else if (is_fcvtsw) begin
      // FCVT.S.W, FCVT.S.WU: Int to Float
      fp_op     = I2F;
      // op_mod: 0 = signed (W), 1 = unsigned (WU)
      fp_op_mod = rs2_field[0];
    end else if (is_fmvxw || is_fmvwx) begin
      // FMV.X.W, FMV.W.X: Bit-level move (bypass FPU)
      use_fpu = 1'b0;
      is_fmv  = 1'b1;
    end else begin
      // Unknown operation - don't use FPU
      use_fpu = 1'b0;
    end
  end

  //
  // Rounding mode selection
  //
  // Use pipelined rounding mode from ID stage for shorter combo path.
  //
  roundmode_e rnd_mode;

  always_comb begin
    if (fp_rm_dyn) begin
      rnd_mode = roundmode_e'(frm_csr);
    end else begin
      rnd_mode = roundmode_e'(fp_rm);
    end
  end

  //
  // Operand preparation
  //
  // fpnew operand usage varies by operation:
  // - FMADD/FNMSUB: a*b+c where a=op[0], b=op[1], c=op[2]
  // - ADD/SUB: 1.0*b+c (a is replaced with 1.0), so we need b=fp_rs1, c=fp_rs2
  // - MUL: a*b+0 (c is replaced with 0), so a=fp_rs1, b=fp_rs2
  // - Other ops: a=op[0], b=op[1]
  //
  logic [2:0][31:0] operands;

  always_comb begin
    if (is_fcvtsw) begin
      // I2F: Integer source on operand[0]
      operands[0] = rs1;
      operands[1] = '0;
      operands[2] = '0;
    end else if (is_fadd || is_fsub) begin
      // ADD computes 1.0 * operands[1] + operands[2]
      // So for FADD rd,rs1,rs2: result = rs1 + rs2
      // We need operands[1]=fp_rs1, operands[2]=fp_rs2
      operands[0] = '0;  // unused (replaced with 1.0)
      operands[1] = fp_rs1;  // first addend
      operands[2] = fp_rs2;  // second addend
    end else begin
      operands[0] = fp_rs1;
      operands[1] = fp_rs2;
      operands[2] = fp_rs3;
    end
  end

  //
  // fpnew instantiation
  //
  // Configuration: FP32 only, no vectors, T-Head divsqrt unit
  //
  localparam fpu_features_t FPU_FEATURES = '{
      Width: 32,
      EnableVectors: 1'b0,
      EnableNanBox: 1'b0,  // No NaN-boxing for 32-bit only
      FpFmtMask: 5'b10000,  // FP32 only
      IntFmtMask: 4'b0010  // INT32 only
  };

  localparam fpu_implementation_t FPU_IMPL = '{
      PipeRegs: '{default: 0},  // No pipeline registers
      UnitTypes: '{
          '{default: PARALLEL},  // ADDMUL
          '{default: MERGED},  // DIVSQRT
          '{default: PARALLEL},  // NONCOMP
          '{default: MERGED}
      },  // CONV
      PipeConfig: BEFORE
  };

  logic           fpu_in_valid;
  logic           fpu_in_ready;
  logic           fpu_out_valid;
  logic    [31:0] fpu_result;
  status_t        fpu_status;
  logic           fpu_busy;

  assign fpu_in_valid = op_valid && use_fpu;

  fpnew_top #(
      .Features      (FPU_FEATURES),
      .Implementation(FPU_IMPL),
      .DivSqrtSel    (TH32),          // Use T-Head E906 divsqrt (FP32 only)
      .TagType       (logic)
  ) u_fpnew (
      .clk_i         (clk),
      .rst_ni        (rst_n),
      .operands_i    (operands),
      .rnd_mode_i    (rnd_mode),
      .op_i          (fp_op),
      .op_mod_i      (fp_op_mod),
      .src_fmt_i     (FP32),
      .dst_fmt_i     (FP32),
      .int_fmt_i     (INT32),
      .vectorial_op_i(1'b0),
      .tag_i         (1'b0),
      .simd_mask_i   (1'b1),
      .in_valid_i    (fpu_in_valid),
      .in_ready_o    (fpu_in_ready),
      .flush_i       (1'b0),
      .result_o      (fpu_result),
      .status_o      (fpu_status),
      .tag_o         (),
      .out_valid_o   (fpu_out_valid),
      .out_ready_i   (1'b1),           // Always ready to accept results
      .busy_o        (fpu_busy),
      .early_valid_o ()
  );

  //
  // Result capture for multi-cycle operations
  //
  // fpnew clears its result after one cycle (since out_ready_i=1).
  // For multi-cycle ops, we register the result when it becomes valid.
  //
  logic [31:0] mc_result_reg;
  logic        mc_result_valid_reg;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mc_result_reg       <= '0;
      mc_result_valid_reg <= 1'b0;
    end else if (is_multicycle && fpu_out_valid) begin
      mc_result_reg       <= fpu_result;
      mc_result_valid_reg <= 1'b1;
    end else if (op_valid && is_multicycle) begin
      // Clear when starting new multi-cycle op
      mc_result_valid_reg <= 1'b0;
    end
  end

  //
  // Result selection
  //
  always_comb begin
    if (is_fmv) begin
      // FMV: direct bit copy
      if (is_fmvxw) begin
        result = fp_rs1;  // FMV.X.W: FP -> INT
      end else begin
        result = rs1;  // FMV.W.X: INT -> FP
      end
    end else if (mc_result_valid_reg) begin
      // Use registered result for multi-cycle ops
      result = mc_result_reg;
    end else begin
      result = fpu_result;
    end
  end

  //
  // Exception flags
  //
  assign fflags = {
    fpu_status.NV, fpu_status.DZ, fpu_status.OF, fpu_status.UF, fpu_status.NX
  };

  //
  // Valid and busy signals
  //
  // For single-cycle ops: result is valid when op_valid is set
  // For multi-cycle ops: result is valid when fpu_out_valid is set
  //
  logic is_multicycle;
  assign is_multicycle = is_fdiv || is_fsqrt;

  always_comb begin
    if (is_fmv) begin
      // FMV bypasses FPU - always single cycle
      result_valid = op_valid;
      busy         = 1'b0;
    end else if (is_multicycle) begin
      // Multi-cycle operations
      result_valid = fpu_out_valid;
      busy         = fpu_busy;
    end else begin
      // Single-cycle FPU operations
      result_valid = op_valid && use_fpu && fpu_out_valid;
      busy         = 1'b0;
    end
  end

  // Unused instruction fields (rd, rs1 handled externally)
  // Unused rs2_field bits (only [0] used for signed/unsigned in FCVT)
  `SVC_UNUSED({fpu_in_ready, instr[19:15], instr[11:7], rs2_field[4:1]});

`else
  // Stub implementation when EXT_F is not defined
  // This module should never be instantiated without EXT_F, but we need
  // a valid module body for iverilog to parse the include.
  assign result_valid = 1'b0;
  assign result       = 32'h0;
  assign fflags       = 5'h0;
  assign busy         = 1'b0;

  `SVC_UNUSED(
      {clk, rst_n, op_valid, instr, frm_csr, fp_rs1, fp_rs2, fp_rs3, rs1});
`endif

endmodule

`endif
