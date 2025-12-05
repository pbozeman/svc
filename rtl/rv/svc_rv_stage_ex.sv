`ifndef SVC_RV_STAGE_EX_SV
`define SVC_RV_STAGE_EX_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_bpred_ex.sv"
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
    parameter int PIPELINED  = 1,
    parameter int FWD        = 1,
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
    input logic ex_mem_flush,

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
    input logic            is_jmp_ex,
    input logic            jb_target_src_ex,
    input logic            is_jal_ex,
    input logic            is_jalr_ex,
    input logic            is_mc_ex,
    input logic            is_m_ex,
    input logic            is_csr_ex,
    input logic            trap_ex,
    input logic [     1:0] trap_code_ex,
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
    input logic [XLEN-1:0] pred_target_ex,

    //
    // Ready/valid interface from ID stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // Forwarding from MEM stage
    //
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // Instruction retirement (for CSR)
    //
    input logic retired,

    //
    // PC control outputs to IF
    //
    output logic [     1:0] pc_sel_ex,
    output logic [XLEN-1:0] pc_redirect_target_ex,
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
    output logic            is_branch_mem,
    output logic            is_jalr_mem,
    output logic            is_jmp_mem,
    output logic            branch_taken_mem,
    output logic            bpred_taken_mem,
    output logic [XLEN-1:0] pred_target_mem,
    output logic            trap_mem,
    output logic [     1:0] trap_code_mem,

    //
    // Ready/valid interface to MEM stage
    //
    output logic m_valid,
    input  logic m_ready,

    //
    // Outputs to hazard unit
    //
    output logic op_active_ex,

    //
    // BTB update interface
    //
    output logic            btb_update_en,
    output logic [XLEN-1:0] btb_update_pc,
    output logic [XLEN-1:0] btb_update_target,
    output logic            btb_update_taken,
    output logic            btb_update_is_ret,
    output logic            btb_update_is_jal
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
  // Multi-cycle operation in progress (past first cycle)
  //
  // Used to select captured operand values during multi-cycle ops. On the
  // first cycle (IDLE state), forwarding from MEM is active and provides the
  // correct values. On subsequent cycles (EXEC state), the pipeline has
  // drained and MEM contains unrelated instructions, so we use the captured
  // values from the first cycle.
  //
  logic      mc_in_progress_ex;
  assign mc_in_progress_ex = (mc_state == MC_STATE_EXEC);

  //
  // Captured operand values for multi-cycle operations
  //
  // When a multi-cycle op starts, we capture the forwarded operand values.
  // These captured values are used on subsequent cycles since the pipeline
  // drains and MEM→EX forwarding would provide stale/wrong values.
  //
  logic [XLEN-1:0] mc_rs1_captured;
  logic [XLEN-1:0] mc_rs2_captured;

  //
  // Next state and output logic
  //
  always_comb begin
    mc_state_next = mc_state;
    op_active_ex  = 1'b0;
    op_en_ex      = 1'b0;

    case (mc_state)
      MC_STATE_IDLE: begin
        if (is_mc_ex && s_valid) begin
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
  // State registers and captured operands
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      mc_state        <= MC_STATE_IDLE;
      mc_rs1_captured <= '0;
      mc_rs2_captured <= '0;
    end else if (!m_valid || m_ready) begin
      mc_state <= mc_state_next;

      //
      // Capture forwarded operands on first cycle of multi-cycle op
      //
      if (mc_state == MC_STATE_IDLE && is_mc_ex && s_valid) begin
        mc_rs1_captured <= fwd_rs1_ex;
        mc_rs2_captured <= fwd_rs2_ex;
      end
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
  // Trap detection (EX stage)
  //
  // Misaligned jump/branch target trap (combined with illegal instruction
  // trap from ID in pipeline register below).
  //
  logic misalign_trap;
  logic jb_active;

  assign jb_active = (is_branch_ex & branch_taken_ex) | is_jal_ex | is_jalr_ex;
  assign misalign_trap = jb_active & (|jb_target_ex[1:0]);

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
      .en(s_valid && s_ready),
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
    logic mispred_not_taken;

    assign mispred_not_taken = mispredicted_ex && !branch_taken_ex;

    always_comb begin
      pc_redirect_target_ex = jb_target_ex;
      if (mispred_not_taken) begin
        pc_redirect_target_ex = pc_ex + 4;
      end
    end
  end else begin : g_no_pc_redirect
    assign pc_redirect_target_ex = jb_target_ex;
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
  //   - JALR misprediction handled in MEM stage (moved for timing)
  //   - Branches handled by predictor, only redirect on misprediction
  //   - Mispredictions trigger recovery
  //
  // Without BPRED:
  //   - Taken branches and all jumps (JAL/JALR) redirect in EX
  //
  logic pc_sel_branch_or_jump;

  if (BPRED != 0) begin : g_bpred_ex_redirect
    //
    // With prediction: only redirect on UNPREDICTED JALR
    // - Predicted JALR: Wait for MEM stage misprediction check (timing opt)
    // - Unpredicted JALR: Redirect immediately in EX (avoid wrong-path execution)
    // - Branches: Never redirect in EX (handled by misprediction logic)
    // - JAL: Predicted in ID stage, never reaches here
    //
    assign pc_sel_branch_or_jump = is_jalr_ex && !bpred_taken_ex;
  end else begin : g_no_bpred_redirect
    //
    // Without prediction: taken branches and all jumps redirect in EX
    //
    assign pc_sel_branch_or_jump = (is_branch_ex & branch_taken_ex) ||
        is_jal_ex || is_jalr_ex;
  end

  //
  // Calculate PC selection mode
  //
  always_comb begin
    if (pc_sel_branch_or_jump || mispredicted_ex) begin
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
      .instret_inc(retired)
  );

  //
  // s_ready generation
  //
  // EX is ready to accept new data when:
  // - Downstream (MEM) is ready or our output register is empty
  // - No multi-cycle operation is in progress
  //
  // This implements backpressure from MEM and internal stalling for multi-cycle ops.
  //

  //
  // EX/MEM Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    //
    // Pipeline register enable
    //
    // Use standard skid buffer enable for all registered signals.
    // m_valid is then combinationally gated by mc_in_progress_ex.
    //
    logic valid_reg;
    logic ex_mem_en;
    assign ex_mem_en = (!valid_reg || m_ready);
    assign m_valid   = valid_reg && !mc_in_progress_ex;
    //
    // Block s_ready when multi-cycle op is active (op_active_ex covers both
    // the starting cycle and execution cycles).
    //
    assign s_ready   = ex_mem_en && !op_active_ex;

    //
    // Multi-cycle operation tracking for valid_reg preservation
    //
    // mc_in_progress_reg: Tracks when we're PAST the first cycle of a
    // multi-cycle op. On the first cycle, we capture valid_reg from s_valid.
    // On subsequent cycles, we preserve valid_reg (don't update from s_valid
    // which may be 0 during multi-cycle execution).
    //
    // This is set when transitioning from IDLE to EXEC (first cycle), and
    // cleared when m_valid && m_ready (result consumed).
    //
    logic mc_in_progress_reg;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        mc_in_progress_reg <= 1'b0;
      end else if (mc_state == MC_STATE_IDLE && is_mc_ex && s_valid &&
                   ex_mem_en) begin
        //
        // First cycle of multi-cycle op - we're about to capture
        //
        mc_in_progress_reg <= 1'b1;
      end else if (m_valid && m_ready) begin
        //
        // Result consumed
        //
        mc_in_progress_reg <= 1'b0;
      end
    end

    //
    // Effective flush for valid_reg: Don't clear during multi-cycle ops
    //
    // The hazard unit sets ex_mem_flush when op_active_ex is high. However,
    // we must preserve valid_reg so that m_valid asserts when the multi-cycle
    // operation completes.
    //
    // mc_in_progress_reg tracks multi-cycle ops AFTER the first cycle.
    // op_active_ex includes the first cycle when we're capturing.
    //
    logic mc_active;
    logic effective_flush;
    assign mc_active       = op_active_ex || mc_in_progress_reg;
    assign effective_flush = ex_mem_flush && !mc_active;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        valid_reg     <= 1'b0;
        reg_write_mem <= 1'b0;
        mem_read_mem  <= 1'b0;
        mem_write_mem <= 1'b0;
        trap_mem      <= 1'b0;
      end else if (ex_mem_en) begin
        //
        // Signals used by forwarding/hazard logic must be explicitly
        // cleared on flush since that logic doesn't check m_valid.
        //
        // For valid_reg:
        // - Clear on effective_flush (not during multi-cycle ops)
        // - Update from s_valid when not in multi-cycle execution OR when
        //   multi-cycle result is consumed (m_valid && m_ready clears
        //   mc_in_progress_reg, but we need to accept new instruction same
        //   cycle)
        // - Preserve during multi-cycle execution otherwise
        //
        if (effective_flush) begin
          valid_reg <= 1'b0;
        end else if (!mc_in_progress_reg || (m_valid && m_ready)) begin
          valid_reg <= s_valid;
        end
        //
        // Other control signals: clear during all flushes
        //
        reg_write_mem <= ex_mem_flush ? 1'b0 : reg_write_ex;
        mem_read_mem  <= ex_mem_flush ? 1'b0 : mem_read_ex;
        mem_write_mem <= ex_mem_flush ? 1'b0 : mem_write_ex;
        trap_mem      <= ex_mem_flush ? 1'b0 : (trap_ex | misalign_trap);
      end
    end

    //
    // payload
    //
    always_ff @(posedge clk) begin
      if (ex_mem_en) begin
        is_branch_mem    <= is_branch_ex;
        is_jalr_mem      <= is_jalr_ex;
        is_jmp_mem       <= is_jmp_ex;
        branch_taken_mem <= branch_taken_ex;
        bpred_taken_mem  <= bpred_taken_ex;
        instr_mem        <= instr_ex;
        res_src_mem      <= res_src_ex;
        rd_mem           <= rd_ex;
        rs2_mem          <= rs2_ex;
        funct3_mem       <= funct3_ex;
        alu_result_mem   <= alu_result_ex;
        rs1_data_mem     <= fwd_rs1_ex;
        rs2_data_mem     <= fwd_rs2_ex;
        pc_plus4_mem     <= pc_plus4_ex;
        jb_target_mem    <= jb_target_ex;
        pred_target_mem  <= pred_target_ex;
        csr_rdata_mem    <= csr_rdata_ex;
        mul_ll_mem       <= mul_ll_ex;
        mul_lh_mem       <= mul_lh_ex;
        mul_hl_mem       <= mul_hl_ex;
        mul_hh_mem       <= mul_hh_ex;
        trap_code_mem    <= misalign_trap ? TRAP_INSTR_MISALIGN : trap_code_ex;
      end

      //
      // m_result_mem: Update during multi-cycle ops to capture final result
      //
      // During multi-cycle ops, ex_mem_en may be 0 (when m_ready=0 and
      // valid_reg=1). But we need m_result_mem to reflect the final
      // division result when the operation completes.
      //
      if (ex_mem_en || mc_in_progress_ex) begin
        m_result_mem <= m_result_ex;
      end
    end

  end else begin : g_passthrough
    assign reg_write_mem = reg_write_ex;
    assign mem_read_mem = mem_read_ex;
    assign mem_write_mem = mem_write_ex;
    assign res_src_mem = res_src_ex;
    assign instr_mem = instr_ex;
    assign rd_mem = rd_ex;
    assign rs2_mem = rs2_ex;
    assign funct3_mem = funct3_ex;
    assign alu_result_mem = alu_result_ex;
    assign rs1_data_mem = fwd_rs1_ex;
    assign rs2_data_mem = fwd_rs2_ex;
    assign pc_plus4_mem = pc_plus4_ex;
    assign jb_target_mem = jb_target_ex;
    assign csr_rdata_mem = csr_rdata_ex;
    assign m_result_mem = m_result_ex;
    assign mul_ll_mem = mul_ll_ex;
    assign mul_lh_mem = mul_lh_ex;
    assign mul_hl_mem = mul_hl_ex;
    assign mul_hh_mem = mul_hh_ex;
    assign is_branch_mem = is_branch_ex;
    assign is_jalr_mem = is_jalr_ex;
    assign is_jmp_mem = is_jmp_ex;
    assign branch_taken_mem = branch_taken_ex;
    assign bpred_taken_mem = bpred_taken_ex;
    assign pred_target_mem = pred_target_ex;
    assign trap_mem = trap_ex | misalign_trap;
    assign trap_code_mem = misalign_trap ? TRAP_INSTR_MISALIGN : trap_code_ex;
    assign m_valid = s_valid && !mc_in_progress_ex;
    //
    // Block s_ready when multi-cycle op is active (op_active_ex covers both
    // the starting cycle and execution cycles).
    //
    assign s_ready = m_ready && !op_active_ex;

    `SVC_UNUSED({ex_mem_flush});
  end

  `SVC_UNUSED({funct7_ex[6:5], funct7_ex[4:0], is_m_ex, is_csr_ex});

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_EX
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)

  //
  // Force reset at start of formal verification
  //
  // This ensures the solver starts from a valid reset state rather than
  // an arbitrary initial state that may violate module invariants.
  //
  // Only apply when verifying this module specifically, not when used as
  // a submodule in other formal checks (like RVFI verification).
  //
  initial assume (!rst_n);
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 1'b0;

  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  //
  // s_valid/s_ready handshake assumptions (input interface)
  //
  // Once s_valid goes high, it must stay high until s_ready
  // All input signals must remain stable while s_valid && !s_ready
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // s_valid must stay high until s_ready
      //
      if ($past(s_valid && !s_ready)) begin
        `FASSUME(a_s_valid_stable, s_valid);
      end
    end
  end

  //
  // m_valid/m_ready handshake assertions (output interface)
  //
  // Once m_valid goes high, it must stay high until m_ready
  // All output signals must remain stable while m_valid && !m_ready
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // Valid must stay high until ready
      //
      if ($past(m_valid && !m_ready)) begin
        `FASSERT(a_m_valid_stable, m_valid);
      end

      //
      // Output signals must be stable while valid && !ready
      //
      if ($past(m_valid && !m_ready)) begin
        `FASSERT(a_reg_write_mem_stable, $stable(reg_write_mem));
        `FASSERT(a_mem_read_mem_stable, $stable(mem_read_mem));
        `FASSERT(a_mem_write_mem_stable, $stable(mem_write_mem));
        `FASSERT(a_res_src_mem_stable, $stable(res_src_mem));
        `FASSERT(a_instr_mem_stable, $stable(instr_mem));
        `FASSERT(a_rd_mem_stable, $stable(rd_mem));
        `FASSERT(a_funct3_mem_stable, $stable(funct3_mem));
        `FASSERT(a_alu_result_mem_stable, $stable(alu_result_mem));
        `FASSERT(a_rs1_data_mem_stable, $stable(rs1_data_mem));
        `FASSERT(a_rs2_data_mem_stable, $stable(rs2_data_mem));
        `FASSERT(a_pc_plus4_mem_stable, $stable(pc_plus4_mem));
        `FASSERT(a_jb_target_mem_stable, $stable(jb_target_mem));
        `FASSERT(a_csr_rdata_mem_stable, $stable(csr_rdata_mem));
        `FASSERT(a_m_result_mem_stable, $stable(m_result_mem));
        `FASSERT(a_mul_ll_mem_stable, $stable(mul_ll_mem));
        `FASSERT(a_mul_lh_mem_stable, $stable(mul_lh_mem));
        `FASSERT(a_mul_hl_mem_stable, $stable(mul_hl_mem));
        `FASSERT(a_mul_hh_mem_stable, $stable(mul_hh_mem));
        `FASSERT(a_is_branch_mem_stable, $stable(is_branch_mem));
        `FASSERT(a_is_jalr_mem_stable, $stable(is_jalr_mem));
        `FASSERT(a_is_jmp_mem_stable, $stable(is_jmp_mem));
        `FASSERT(a_branch_taken_mem_stable, $stable(branch_taken_mem));
        `FASSERT(a_bpred_taken_mem_stable, $stable(bpred_taken_mem));
        `FASSERT(a_pred_target_mem_stable, $stable(pred_target_mem));
        `FASSERT(a_trap_mem_stable, $stable(trap_mem));
        `FASSERT(a_trap_code_mem_stable, $stable(trap_code_mem));
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // Cover back-to-back valid transfers
      //
      `FCOVER(c_back_to_back, $past(m_valid && m_ready) && m_valid);

      //
      // Cover stalled transfer (valid high, ready low for a cycle)
      //
      `FCOVER(c_stalled, $past(m_valid && !m_ready) && m_valid && m_ready);
    end
  end

  //
  // Multi-cycle operation assertions (pipelined mode only)
  //
  if (PIPELINED != 0) begin : g_mc_formal
    //
    // mc_in_progress_reg must clear when result is consumed
    //
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // After m_valid && m_ready handshake, mc_in_progress_reg must be 0
        // UNLESS a new mc op started in the same cycle
        //
        if ($past(m_valid && m_ready) && !$past(is_mc_ex && s_valid)) begin
          `FASSERT(a_mc_clears_on_handshake, !g_registered.mc_in_progress_reg);
        end

        //
        // mc_in_progress_reg should only be set for multi-cycle ops
        //
        if ($rose(g_registered.mc_in_progress_reg)) begin
          `FASSERT(a_mc_set_only_for_mc_op, $past(is_mc_ex && s_valid));
        end

        //
        // When mc_state is IDLE and no mc op starting, mc_in_progress_reg
        // should eventually clear (after handshake)
        //
        if (mc_state == MC_STATE_IDLE && !is_mc_ex) begin
          //
          // If we're idle with no mc op, and m_valid && m_ready happened,
          // mc_in_progress_reg must be 0
          //
          if ($past(m_valid && m_ready)) begin
            `FASSERT(a_mc_idle_clears, !g_registered.mc_in_progress_reg);
          end
        end

        //
        // op_active_ex should only be high during multi-cycle execution
        //
        if (op_active_ex) begin
          `FASSERT(a_op_active_implies_mc,
                   (mc_state == MC_STATE_IDLE && is_mc_ex) ||
                       (mc_state == MC_STATE_EXEC && m_busy_ex));
        end

        //
        // When DIV completes (mc_state goes IDLE, was EXEC), if there's no
        // new mc op starting, op_active_ex should be 0
        //
        if ($past(mc_state == MC_STATE_EXEC) && mc_state == MC_STATE_IDLE) begin
          if (!is_mc_ex) begin
            `FASSERT(a_op_active_clears_on_complete, !op_active_ex);
          end
        end

        //
        // s_ready should be low during multi-cycle execution
        //
        if (mc_state == MC_STATE_EXEC && m_busy_ex) begin
          `FASSERT(a_sready_low_during_mc, !s_ready);
        end

        //
        // After mc op completes and result consumed, s_ready should be high
        // (assuming no backpressure from downstream)
        //
        if ($past(m_valid && m_ready) && !op_active_ex && m_ready) begin
          `FASSERT(a_sready_high_after_mc, s_ready);
        end
      end
    end

    //
    // Cover multi-cycle operation scenarios
    //
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // Cover: DIV starts
        //
        `FCOVER(c_mc_starts, $rose(op_active_ex) && is_mc_ex);

        //
        // Cover: DIV completes and result consumed same cycle
        //
        `FCOVER(c_mc_complete_immediate, $past(mc_state == MC_STATE_EXEC
                ) && mc_state == MC_STATE_IDLE && m_valid && m_ready);

        //
        // Cover: DIV completes but result held (m_ready=0)
        //
        `FCOVER(c_mc_complete_held, $past(mc_state == MC_STATE_EXEC
                ) && mc_state == MC_STATE_IDLE && m_valid && !m_ready);

        //
        // Cover: Back-to-back DIV operations
        //
        `FCOVER(c_mc_back_to_back, $past(
                m_valid && m_ready && g_registered.mc_in_progress_reg
                ) && is_mc_ex && s_valid);

        //
        // Cover: DIV followed by non-mc instruction
        //
        `FCOVER(c_mc_then_normal, $past(
                m_valid && m_ready && g_registered.mc_in_progress_reg
                ) && !is_mc_ex && s_valid);
      end
    end
  end

  //
  // State machine invariants
  //
  // Ensure the mc FSM only does intended transitions and never sits in
  // EXEC without a pending operation.
  //
  if (PIPELINED != 0) begin : g_mc_state_invariants
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // mc_state must always be a legal enum value
        //
        `FASSERT(a_mc_state_legal,
                 mc_state == MC_STATE_IDLE || mc_state == MC_STATE_EXEC);

        //
        // Only transition IDLE -> EXEC when we actually start a mc op
        //
        if ($past(mc_state) == MC_STATE_IDLE && mc_state == MC_STATE_EXEC) begin
          `FASSERT(a_mc_idle_to_exec_only_on_mc, $past(
                   is_mc_ex && s_valid && g_registered.ex_mem_en));
        end

        //
        // Only transition EXEC -> IDLE when divider reports not busy
        //
        if ($past(mc_state) == MC_STATE_EXEC && mc_state == MC_STATE_IDLE) begin
          `FASSERT(a_mc_exec_to_idle_only_when_not_busy, !$past(m_busy_ex));
        end

        //
        // While busy, we must stay in EXEC
        //
        if ($past(mc_state) == MC_STATE_EXEC && $past(m_busy_ex)) begin
          `FASSERT(a_mc_stays_exec_while_busy, mc_state == MC_STATE_EXEC);
        end

        //
        // We should never be in EXEC without having an active op
        //
        if (mc_state == MC_STATE_EXEC) begin
          `FASSERT(a_mc_exec_implies_active, op_active_ex || !m_busy_ex);
        end
      end
    end
  end

  //
  // Operand capture & stability during mc ops
  //
  // Verify captured operands are correct and stable during multi-cycle ops.
  //
  if (PIPELINED != 0) begin : g_mc_operand_checks
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // On the first cycle of a mc op, captured operands must equal the
        // forwarded values we saw on that cycle.
        //
        if (mc_state == MC_STATE_EXEC && $past(
                mc_state == MC_STATE_IDLE && is_mc_ex && s_valid &&
                    g_registered.ex_mem_en
            )) begin
          `FASSERT(a_mc_capture_rs1_correct, mc_rs1_captured == $past(fwd_rs1_ex
                   ));
          `FASSERT(a_mc_capture_rs2_correct, mc_rs2_captured == $past(fwd_rs2_ex
                   ));
        end

        //
        // Once in EXEC, captured operands must not change
        //
        if ($past(mc_state == MC_STATE_EXEC) && mc_state == MC_STATE_EXEC) begin
          `FASSERT(a_mc_rs1_captured_stable, $stable(mc_rs1_captured));
          `FASSERT(a_mc_rs2_captured_stable, $stable(mc_rs2_captured));
        end
      end
    end
  end

  //
  // Handshake vs mc_state / valid_reg / m_valid invariants
  //
  if (PIPELINED != 0) begin : g_mc_handshake_invariants
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // We only assert m_valid when the mc FSM is idle
        //
        if (m_valid) begin
          `FASSERT(a_m_valid_implies_idle,
                   mc_state == MC_STATE_IDLE && !mc_in_progress_ex);
        end

        //
        // If we're in EXEC, the EX/MEM valid_reg must be holding the
        // instruction associated with this mc op.
        //
        if (mc_state == MC_STATE_EXEC) begin
          `FASSERT(a_exec_implies_valid_reg, g_registered.valid_reg);
        end

        //
        // When we start a mc op, valid_reg must get set if s_valid was high.
        //
        if ($past(
                mc_state == MC_STATE_IDLE && is_mc_ex && s_valid &&
                    g_registered.ex_mem_en
            )) begin
          `FASSERT(a_mc_start_sets_valid_reg, g_registered.valid_reg);
        end

        //
        // While op_active_ex, s_ready must be low
        //
        if (op_active_ex) begin
          `FASSERT(a_op_active_blocks_s_ready, !s_ready);
        end

        //
        // If EX accepts a new non-mc instruction, we must not be in EXEC
        // in the next cycle.
        //
        if ($past(s_valid && s_ready && !is_mc_ex)) begin
          `FASSERT(a_non_mc_accept_keeps_idle, mc_state == MC_STATE_IDLE);
        end
      end
    end
  end

  //
  // Contract with m_busy_ex / divider (EXT_M enabled)
  //
  if (PIPELINED != 0 && EXT_M != 0) begin : g_mc_busy_contract
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // Divider 'busy' should never be asserted when we're in IDLE and
        // no mc op is active.
        //
        if (mc_state == MC_STATE_IDLE && !is_mc_ex) begin
          `FASSERT(a_idle_not_busy, !m_busy_ex);
        end
      end
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
