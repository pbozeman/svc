`ifndef SVC_RV_STAGE_EX_SV
`define SVC_RV_STAGE_EX_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_csr.sv"
`include "svc_rv_ext_mul_ex.sv"
`include "svc_rv_ext_div.sv"
`include "svc_rv_fwd_ex.sv"

//
// RISC-V Execute (EX) Stage
//
// Encapsulates all logic for the execute pipeline stage:
// - ALU operations
// - Branch comparison and target calculation
// - Jump target calculation
// - CSR operations
// - M extension (multiply/divide)
// - Data forwarding from MEM/WB stages
// - Multi-cycle operation control
// - EX/MEM pipeline register
//
// This stage performs arithmetic operations, branch decisions, and
// prepares results for the memory stage.
//
module svc_rv_stage_ex #(
    parameter int XLEN       = 32,
    parameter int PIPELINED  = 0,
    parameter int FWD        = 0,
    parameter int MEM_TYPE   = 0,
    parameter int BPRED      = 0,
    parameter int BTB_ENABLE = 0,
    parameter int EXT_ZMMUL  = 0,
    parameter int EXT_M      = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic ex_mem_stall,

    //
    // From ID stage
    //
    input logic            reg_write_ex,
    input logic            mem_read_ex,
    input logic            mem_write_ex,
    input logic [     1:0] alu_a_src_ex,
    input logic            alu_b_src_ex,
    input logic [     1:0] alu_instr_ex,
    input logic [     2:0] res_src_ex,
    input logic            is_branch_ex,
    input logic            is_jump_ex,
    input logic            jb_target_src_ex,
    input logic            is_mc_ex,
    input logic [    31:0] instr_ex,
    input logic [     4:0] rd_ex,
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic [     2:0] funct3_ex,
    input logic [     6:0] funct7_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,
    input logic [XLEN-1:0] imm_ex,
    input logic [XLEN-1:0] pc_ex,
    input logic [XLEN-1:0] pc_plus4_ex,
    input logic            bpred_taken_ex,

    //
    // Forwarding from MEM stage
    //
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // Instruction retirement (for CSR)
    //
    input logic instr_retired,

    //
    // PC control outputs to IF
    //
    output logic [     1:0] pc_sel_ex,
    output logic [XLEN-1:0] pc_redirect_target,
    output logic            mispredicted_ex,

    //
    // Outputs to MEM stage
    //
    output logic            reg_write_mem,
    output logic            mem_read_mem,
    output logic            mem_write_mem,
    output logic [     2:0] res_src_mem,
    output logic [    31:0] instr_mem,
    output logic [     4:0] rd_mem,
    output logic [     4:0] rs2_mem,
    output logic [     2:0] funct3_mem,
    output logic [XLEN-1:0] alu_result_mem,
    output logic [XLEN-1:0] rs1_data_mem,
    output logic [XLEN-1:0] rs2_data_mem,
    output logic [XLEN-1:0] pc_plus4_mem,
    output logic [XLEN-1:0] jb_target_mem,
    output logic [XLEN-1:0] csr_rdata_mem,
    output logic [XLEN-1:0] m_result_mem,
    output logic [XLEN-1:0] mul_ll_mem,
    output logic [XLEN-1:0] mul_lh_mem,
    output logic [XLEN-1:0] mul_hl_mem,
    output logic [XLEN-1:0] mul_hh_mem,

    //
    // Outputs to hazard unit
    //
    output logic is_csr_ex,
    output logic is_m_ex,
    output logic op_active_ex,

    //
    // BTB update interface
    //
    output logic            btb_update_en,
    output logic [XLEN-1:0] btb_update_pc,
    output logic [XLEN-1:0] btb_update_target,
    output logic            btb_update_taken
);

  `include "svc_rv_defs.svh"

  //
  // EX stage internal signals
  //
  logic [     3:0] alu_op_ex;
  logic [XLEN-1:0] alu_a_ex;
  logic [XLEN-1:0] alu_b_ex;
  logic [XLEN-1:0] alu_result_ex;
  logic [XLEN-1:0] jb_target_ex;

  //
  // Multi-cycle operation control
  //
  logic            op_en_ex;
  logic [XLEN-1:0] m_result_ex;
  logic            m_busy_ex;

  //
  // M extension partial products (for 2-stage multiply)
  //
  logic [XLEN-1:0] mul_ll_ex;
  logic [XLEN-1:0] mul_lh_ex;
  logic [XLEN-1:0] mul_hl_ex;
  logic [XLEN-1:0] mul_hh_ex;

  //
  // Branch signals
  //
  logic            branch_taken_ex;

  //
  // CSR signals
  //
  logic [XLEN-1:0] csr_rdata_ex;

  //
  // Decode result sources
  //
  assign is_csr_ex = (res_src_ex == RES_CSR);
  assign is_m_ex   = (res_src_ex == RES_M);

  //
  // ALU Decoder
  //
  svc_rv_alu_dec alu_dec (
      .alu_instr(alu_instr_ex),
      .funct3   (funct3_ex),
      .funct7_b5(funct7_ex[5]),
      .op_b5    (instr_ex[5]),
      .alu_op   (alu_op_ex)
  );

  //
  // Data forwarding unit
  //
  logic [XLEN-1:0] fwd_rs1_ex;
  logic [XLEN-1:0] fwd_rs2_ex;

  svc_rv_fwd_ex #(
      .XLEN    (XLEN),
      .FWD     ((PIPELINED != 0 && FWD != 0) ? 1 : 0),
      .MEM_TYPE(MEM_TYPE)
  ) forward (
      .*
  );

  //
  // ALU A input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (3)
  ) mux_alu_a (
      .sel (alu_a_src_ex),
      .data({pc_ex, {XLEN{1'b0}}, fwd_rs1_ex}),
      .out (alu_a_ex)
  );

  //
  // ALU B input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_alu_b (
      .sel (alu_b_src_ex),
      .data({imm_ex, fwd_rs2_ex}),
      .out (alu_b_ex)
  );

  //
  // ALU
  //
  svc_rv_alu #(
      .XLEN(XLEN)
  ) alu (
      .a     (alu_a_ex),
      .b     (alu_b_ex),
      .alu_op(alu_op_ex),
      .result(alu_result_ex)
  );

  //
  // Multi-cycle operation control state machine
  //
  // Manages the lifecycle of multi-cycle operations (DIV/REM) in EX stage.
  //
  // States:
  //   IDLE: No multi-cycle operation active
  //   EXEC: Multi-cycle operation executing
  //
  // For single-cycle M ops (MUL): IDLE -> IDLE (never enter EXEC)
  // For multi-cycle M ops (DIV/REM): IDLE -> EXEC -> IDLE
  //
  typedef enum logic {
    MC_STATE_IDLE,
    MC_STATE_EXEC
  } mc_state_t;

  mc_state_t mc_state;
  mc_state_t mc_state_next;

  //
  // Next state and output logic
  //
  always_comb begin
    mc_state_next = mc_state;
    op_active_ex  = 1'b0;
    op_en_ex      = 1'b0;

    case (mc_state)
      MC_STATE_IDLE: begin
        if (is_mc_ex) begin
          op_en_ex      = 1'b1;
          op_active_ex  = 1'b1;
          mc_state_next = MC_STATE_EXEC;
        end
      end

      MC_STATE_EXEC: begin
        if (!m_busy_ex) begin
          mc_state_next = MC_STATE_IDLE;
        end else begin
          op_active_ex = 1'b1;
        end
      end

      default: begin
        mc_state_next = MC_STATE_IDLE;
      end
    endcase
  end

  //
  // State registers
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      mc_state <= MC_STATE_IDLE;
    end else begin
      mc_state <= mc_state_next;
    end
  end

  //
  // M Extension Units
  //
  // Multiply and division are split into separate units:
  // - Multiply: combinational 16-bit partial products (EX stage)
  // - Division: sequential 32-cycle operation (multi-cycle)
  //
  // ZMMUL: multiply only
  // M:     multiply + division
  //
  if (EXT_ZMMUL != 0 || EXT_M != 0) begin : g_m_ext
    //
    // Multiply unit (used by both ZMMUL and M)
    //
    // Produces 16-bit partial products that are combined in MEM stage.
    // This is a pure combinational unit.
    //
    svc_rv_ext_mul_ex ext_mul (
        .rs1   (fwd_rs1_ex),
        .rs2   (fwd_rs2_ex),
        .op    (funct3_ex),
        .mul_ll(mul_ll_ex),
        .mul_lh(mul_lh_ex),
        .mul_hl(mul_hl_ex),
        .mul_hh(mul_hh_ex)
    );

    if (EXT_M != 0) begin : g_div
      //
      // Division unit (only for full M extension)
      //
      // Multi-cycle sequential divider.
      // Only enable for division operations (funct3[2] = 1).
      //
      logic div_en;
      logic div_busy;

      assign div_en = op_en_ex && funct3_ex[2];

      svc_rv_ext_div ext_div (
          .clk   (clk),
          .rst_n (rst_n),
          .en    (div_en),
          .rs1   (fwd_rs1_ex),
          .rs2   (fwd_rs2_ex),
          .op    (funct3_ex),
          .busy  (div_busy),
          .result(m_result_ex)
      );

      assign m_busy_ex = div_busy;

    end else begin : g_no_div
      //
      // ZMMUL: no division unit
      //
      assign m_result_ex = '0;
      assign m_busy_ex   = 1'b0;

      `SVC_UNUSED({op_en_ex, op_active_ex});
    end

  end else begin : g_no_m_ext
    //
    // No M extension
    //
    assign m_result_ex = '0;
    assign m_busy_ex   = 1'b0;
    assign mul_ll_ex   = '0;
    assign mul_lh_ex   = '0;
    assign mul_hl_ex   = '0;
    assign mul_hh_ex   = '0;

    `SVC_UNUSED({op_en_ex, op_active_ex});
  end

  //
  // Jump/Branch target calculation
  //
  // Two target address calculation modes:
  //
  // 1. PC-relative (JAL and all branches):
  //    target = PC + offset
  //    Used by: JAL, BEQ, BNE, BLT, BGE, BLTU, BGEU
  //
  // 2. Register-indirect (JALR only):
  //    target = (rs1 + offset) & ~1
  //    The ALU computes rs1+offset, then LSB is cleared per RISC-V spec.
  //    This ensures all jump targets are aligned to even addresses
  //
  logic [XLEN-1:0] jb_target_jalr;
  logic [XLEN-1:0] jb_target_pc_rel;

  //
  // JALR target: ALU result with LSB cleared
  //
  assign jb_target_jalr   = {alu_result_ex[XLEN-1:1], 1'b0};

  //
  // PC-relative target: Dedicated adder for JAL and branches
  //
  assign jb_target_pc_rel = pc_ex + imm_ex;

  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_jb_target (
      .sel (jb_target_src_ex),
      .data({jb_target_jalr, jb_target_pc_rel}),
      .out (jb_target_ex)
  );

  //
  // Branch comparison
  //
  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) bcmp (
      .a_ex           (fwd_rs1_ex),
      .b_ex           (fwd_rs2_ex),
      .funct3         (funct3_ex),
      .branch_taken_ex(branch_taken_ex)
  );

  //
  // Branch prediction and misprediction detection
  //
  svc_rv_bpred_ex #(
      .XLEN      (XLEN),
      .BPRED     (BPRED),
      .BTB_ENABLE(BTB_ENABLE)
  ) bpred (
      .*
  );

  //
  // PC redirect target calculation
  //
  // On misprediction, redirect to:
  // - pc + 4 if predicted taken but actually not-taken
  // - jb_target if predicted not-taken but actually taken
  // On actual taken branch/jump: jb_target
  //
  if (BPRED != 0) begin : g_pc_redirect
    always_comb begin
      case (1'b1)
        mispredicted_ex && branch_taken_ex:  pc_redirect_target = jb_target_ex;
        mispredicted_ex && !branch_taken_ex: pc_redirect_target = pc_ex + 4;
        default:                             pc_redirect_target = jb_target_ex;
      endcase
    end
  end else begin : g_no_pc_redirect
    assign pc_redirect_target = jb_target_ex;
  end

  //
  // PC selection logic
  //
  // Determines which PC source to use based on control flow and prediction:
  // - PC_SEL_REDIRECT: Actual taken branches/jumps or mispredictions
  // - PC_SEL_PREDICTED: Handled by ID stage (never set here)
  // - PC_SEL_SEQUENTIAL: Normal execution (default)
  //
  // When BPRED is enabled:
  //   - JAL is handled by predictor in ID stage, so don't redirect in EX
  //   - JALR still needs EX stage redirect (requires ALU result)
  //   - Branches handled by predictor, only redirect on misprediction
  //   - Mispredictions trigger recovery
  //
  logic pc_sel_jump;
  logic pc_sel_branch;

  if (BPRED != 0) begin : g_pc_sel_jump
    //
    // Only JALR triggers redirect (JAL is predicted in ID)
    //
    assign pc_sel_jump   = is_jump_ex && jb_target_src_ex;

    //
    // Branches don't trigger redirect (handled by predictor or misprediction)
    //
    assign pc_sel_branch = 1'b0;
  end else begin : g_no_pc_sel_jump
    //
    // All jumps trigger redirect
    //
    assign pc_sel_jump   = is_jump_ex;

    //
    // Taken branches trigger redirect
    //
    assign pc_sel_branch = is_branch_ex & branch_taken_ex;
  end

  //
  // Calculate PC selection mode
  //
  always_comb begin
    if (pc_sel_branch || pc_sel_jump || mispredicted_ex) begin
      pc_sel_ex = PC_SEL_REDIRECT;
    end else begin
      pc_sel_ex = PC_SEL_SEQUENTIAL;
    end
  end


  //
  // CSR (Control and Status Registers) - Zicntr
  //
  svc_rv_csr csr (
      .clk        (clk),
      .rst_n      (rst_n),
      .csr_addr   (imm_ex[11:0]),
      .csr_rdata  (csr_rdata_ex),
      .instret_inc(instr_retired)
  );

  //
  // EX/MEM Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        reg_write_mem  <= 1'b0;
        mem_read_mem   <= 1'b0;
        mem_write_mem  <= 1'b0;
        res_src_mem    <= '0;
        instr_mem      <= I_NOP;
        rd_mem         <= '0;
        rs2_mem        <= '0;
        funct3_mem     <= '0;
        alu_result_mem <= '0;
        rs1_data_mem   <= '0;
        rs2_data_mem   <= '0;
        pc_plus4_mem   <= '0;
        jb_target_mem  <= '0;
        csr_rdata_mem  <= '0;
        m_result_mem   <= '0;
        mul_ll_mem     <= '0;
        mul_lh_mem     <= '0;
        mul_hl_mem     <= '0;
        mul_hh_mem     <= '0;
      end else if (!ex_mem_stall) begin
        reg_write_mem  <= reg_write_ex;
        mem_read_mem   <= mem_read_ex;
        mem_write_mem  <= mem_write_ex;
        res_src_mem    <= res_src_ex;
        instr_mem      <= instr_ex;
        rd_mem         <= rd_ex;
        rs2_mem        <= rs2_ex;
        funct3_mem     <= funct3_ex;
        alu_result_mem <= alu_result_ex;
        rs1_data_mem   <= fwd_rs1_ex;
        rs2_data_mem   <= fwd_rs2_ex;
        pc_plus4_mem   <= pc_plus4_ex;
        jb_target_mem  <= jb_target_ex;
        csr_rdata_mem  <= csr_rdata_ex;
        m_result_mem   <= m_result_ex;
        mul_ll_mem     <= mul_ll_ex;
        mul_lh_mem     <= mul_lh_ex;
        mul_hl_mem     <= mul_hl_ex;
        mul_hh_mem     <= mul_hh_ex;
      end
    end

  end else begin : g_passthrough
    assign reg_write_mem  = reg_write_ex;
    assign mem_read_mem   = mem_read_ex;
    assign mem_write_mem  = mem_write_ex;
    assign res_src_mem    = res_src_ex;
    assign instr_mem      = instr_ex;
    assign rd_mem         = rd_ex;
    assign rs2_mem        = rs2_ex;
    assign funct3_mem     = funct3_ex;
    assign alu_result_mem = alu_result_ex;
    assign rs1_data_mem   = fwd_rs1_ex;
    assign rs2_data_mem   = fwd_rs2_ex;
    assign pc_plus4_mem   = pc_plus4_ex;
    assign jb_target_mem  = jb_target_ex;
    assign csr_rdata_mem  = csr_rdata_ex;
    assign m_result_mem   = m_result_ex;
    assign mul_ll_mem     = mul_ll_ex;
    assign mul_lh_mem     = mul_lh_ex;
    assign mul_hl_mem     = mul_hl_ex;
    assign mul_hh_mem     = mul_hh_ex;

    `SVC_UNUSED({ex_mem_stall});
  end

  `SVC_UNUSED({funct7_ex[6:5], funct7_ex[4:0]});

endmodule

`endif
