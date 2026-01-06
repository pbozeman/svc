`ifndef SVC_RV_STAGE_ID_SV
`define SVC_RV_STAGE_ID_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_bpred_id.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_fwd_id.sv"
`include "svc_rv_pipe_ctrl.sv"
`include "svc_rv_pipe_data.sv"
`include "svc_rv_regfile.sv"

//
// RISC-V Instruction Decode (ID) Stage
//
// Encapsulates all logic for the instruction decode pipeline stage:
// - Instruction decoder
// - Register file reads
// - Immediate value generation
// - Branch prediction logic
// - ID/EX pipeline register
//
// This stage decodes instructions, reads register operands, and prepares
// control signals for the execute stage.
//
module svc_rv_stage_id #(
    parameter int XLEN        = 32,
    parameter int MEM_TYPE    = 0,
    parameter int PIPELINED   = 1,
    parameter int FWD_REGFILE = 1,
    parameter int BPRED       = 0,
    parameter int BTB_ENABLE  = 0,
    parameter int RAS_ENABLE  = 0,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0
) (
    input logic clk,
    input logic rst_n,

    // Hazard control
    input logic data_hazard_id,
    input logic id_ex_flush,

    // Stall
    input logic stall_id,
    input logic dmem_stall,

    // From IF stage (s_ready removed, stall controls upstream flow)
    input logic s_valid,

    input logic [    31:0] instr_id,
    input logic [    31:0] pc_id,
    input logic [    31:0] pc_plus4_id,
    input logic            btb_hit_id,
    input logic            btb_pred_taken_id,
    input logic [XLEN-1:0] btb_tgt_id,
    input logic            ras_valid_id,
    input logic [XLEN-1:0] ras_tgt_id,

    // Write-back from WB stage
    input logic        reg_write_wb,
    input logic [ 4:0] rd_wb,
    input logic [31:0] rd_data_wb,

    // MEM stage forwarding inputs
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] ld_data_mem,

    // Outputs to EX stage
    output logic m_valid,

    output logic            reg_write_ex,
    output logic            mem_read_ex,
    output logic            mem_write_ex,
    output logic [     1:0] alu_a_src_ex,
    output logic            alu_b_src_ex,
    output logic [     1:0] alu_instr_ex,
    output logic [     2:0] res_src_ex,
    output logic            is_branch_ex,
    output logic            is_jmp_ex,
    output logic            jb_tgt_src_ex,
    output logic            is_mc_ex,
    output logic            is_m_ex,
    output logic            is_csr_ex,
    output logic            is_jal_ex,
    output logic            is_jalr_ex,
    output logic            trap_ex,
    output logic [     1:0] trap_code_ex,
    output logic            is_ebreak_ex,
    output logic [    31:0] instr_ex,
    output logic [     4:0] rd_ex,
    output logic [     4:0] rs1_ex,
    output logic [     4:0] rs2_ex,
    output logic [     2:0] funct3_ex,
    output logic [     6:0] funct7_ex,
    output logic [XLEN-1:0] rs1_data_ex,
    output logic [XLEN-1:0] rs2_data_ex,
    output logic [XLEN-1:0] imm_ex,
    output logic [XLEN-1:0] pc_ex,
    output logic [XLEN-1:0] pc_plus4_ex,
    output logic            bpred_taken_ex,
    output logic [XLEN-1:0] pred_tgt_ex,

    // Outputs to hazard unit
    output logic [4:0] rs1_id,
    output logic [4:0] rs2_id,
    output logic       rs1_used_id,
    output logic       rs2_used_id,
    output logic       is_mc_id,

    // Branch prediction outputs to IF stage
    output logic [     1:0] pc_sel_id,
    output logic [XLEN-1:0] pred_tgt,
    output logic            pred_taken_id,
    output logic            is_jalr_id
);

  `include "svc_rv_defs.svh"

  //
  // ID stage signals
  //
  logic            reg_write_id;
  logic            mem_read_id;
  logic            mem_write_id;
  logic [     1:0] alu_a_src_id;
  logic            alu_b_src_id;
  logic [     1:0] alu_instr_id;
  logic [     2:0] res_src_id;
  logic [     2:0] imm_type;
  logic            is_branch_id;
  logic            is_jmp_id;
  logic            jb_tgt_src_id;
  logic            is_m_id;
  logic            is_csr_id;
  logic            is_jal_id;
  logic            is_ebreak_id;
  logic            instr_invalid_id;
  logic [     4:0] rd_id;
  logic [     2:0] funct3_id;
  logic [     6:0] funct7_id;
  logic [XLEN-1:0] imm_i;
  logic [XLEN-1:0] imm_s;
  logic [XLEN-1:0] imm_b;
  logic [XLEN-1:0] imm_u;
  logic [XLEN-1:0] imm_j;
  logic [XLEN-1:0] imm_id;
  logic [XLEN-1:0] rs1_data_id;
  logic [XLEN-1:0] rs2_data_id;
  logic            bpred_taken_id;

  //
  // Instruction Decoder
  //
  svc_rv_idec #(
      .XLEN (XLEN),
      .EXT_M(EXT_ZMMUL | EXT_M)
  ) idec (
      .instr        (instr_id),
      .reg_write    (reg_write_id),
      .mem_read     (mem_read_id),
      .mem_write    (mem_write_id),
      .alu_a_src    (alu_a_src_id),
      .alu_b_src    (alu_b_src_id),
      .alu_instr    (alu_instr_id),
      .res_src      (res_src_id),
      .imm_type     (imm_type),
      .is_branch    (is_branch_id),
      .is_jmp       (is_jmp_id),
      .jb_tgt_src   (jb_tgt_src_id),
      .is_m         (is_m_id),
      .is_csr       (is_csr_id),
      .is_ebreak    (is_ebreak_id),
      .is_jal       (is_jal_id),
      .is_jalr      (is_jalr_id),
      .instr_invalid(instr_invalid_id),
      .rd           (rd_id),
      .rs1          (rs1_id),
      .rs2          (rs2_id),
      .funct3       (funct3_id),
      .funct7       (funct7_id),
      .rs1_used     (rs1_used_id),
      .rs2_used     (rs2_used_id),
      .imm_i        (imm_i),
      .imm_s        (imm_s),
      .imm_b        (imm_b),
      .imm_u        (imm_u),
      .imm_j        (imm_j)
  );

  //
  // Immediate mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (5)
  ) mux_imm (
      .sel (imm_type),
      .data({imm_u, imm_j, imm_b, imm_s, imm_i}),
      .out (imm_id)
  );

  //
  // Multi-cycle operation detection
  //
  // Identifies operations that require multiple cycles to complete.
  // Currently: DIV/REM (funct3[2]=1) from M extension (not ZMMUL)
  //
  // M-extension detection: R-type instruction with funct7[0]=1
  //
  if (EXT_M != 0) begin : g_ext_m_mc
    assign is_mc_id = is_m_id && funct3_id[2];
  end else begin : g_not_ext_m_mc
    assign is_mc_id = 1'b0;
  end

  //
  // Register File
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(FWD_REGFILE)
  ) regfile (
      .clk     (clk),
      .rs1_addr(rs1_id),
      .rs1_data(rs1_data_id),
      .rs2_addr(rs2_id),
      .rs2_data(rs2_data_id),
      .rd_en   (reg_write_wb && !dmem_stall),
      .rd_addr (rd_wb),
      .rd_data (rd_data_wb)
  );

  //
  // ID Stage Forwarding Unit
  //
  logic [XLEN-1:0] fwd_rs1_id;
  logic [XLEN-1:0] fwd_rs2_id;

  svc_rv_fwd_id #(
      .XLEN    (XLEN),
      .MEM_TYPE(MEM_TYPE)
  ) fwd_id (
      .clk          (clk),
      .rs1_id       (rs1_id),
      .rs2_id       (rs2_id),
      .rs1_data_id  (rs1_data_id),
      .rs2_data_id  (rs2_data_id),
      .rd_mem       (rd_mem),
      .reg_write_mem(reg_write_mem),
      .res_src_mem  (res_src_mem),
      .result_mem   (result_mem),
      .ld_data_mem  (ld_data_mem),
      .rd_wb        (rd_wb),
      .reg_write_wb (reg_write_wb),
      .rd_data_wb   (rd_data_wb),
      .fwd_rs1_id   (fwd_rs1_id),
      .fwd_rs2_id   (fwd_rs2_id)
  );

  //
  // Branch Prediction: RAS/BTB with static BTFNT fallback
  //
  svc_rv_bpred_id #(
      .XLEN      (XLEN),
      .BPRED     (BPRED),
      .BTB_ENABLE(BTB_ENABLE),
      .RAS_ENABLE(RAS_ENABLE)
  ) bpred (
      .pc_id            (pc_id),
      .imm_id           (imm_id),
      .is_branch_id     (is_branch_id),
      .is_jal_id        (is_jal_id),
      .is_jalr_id       (is_jalr_id),
      .btb_hit_id       (btb_hit_id),
      .btb_pred_taken_id(btb_pred_taken_id),
      .ras_valid_id     (ras_valid_id),
      .ras_tgt_id       (ras_tgt_id),
      .pc_sel_id        (pc_sel_id),
      .pred_tgt         (pred_tgt),
      .pred_taken_id    (pred_taken_id),
      .bpred_taken_id   (bpred_taken_id)
  );

  // ==========================================================================
  // ID/EX Pipeline Register
  // ==========================================================================

  //
  // Pipeline control
  //
  (* max_fanout = 32 *)logic advance;
  logic flush;
  logic bubble;

  svc_rv_pipe_ctrl #(
      .REG(PIPELINED)
  ) pipe_ctrl (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (s_valid),
      .valid_o  (m_valid),
      .stall_i  (stall_id),
      .flush_i  (id_ex_flush),
      .bubble_i (data_hazard_id),
      .advance_o(advance),
      .flush_o  (flush),
      .bubble_o (bubble)
  );

  //
  // Processor control signals
  //
  svc_rv_pipe_data #(
      .WIDTH(8),
      .REG  (PIPELINED)
  ) pipe_ctrl_signals (
      .clk(clk),
      .rst_n(rst_n),
      .advance(advance),
      .flush(flush),
      .bubble(bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i({
        reg_write_id,
        mem_read_id,
        mem_write_id,
        is_branch_id,
        is_jmp_id,
        is_jal_id,
        is_jalr_id,
        instr_invalid_id
      }),
      .data_o({
        reg_write_ex,
        mem_read_ex,
        mem_write_ex,
        is_branch_ex,
        is_jmp_ex,
        is_jal_ex,
        is_jalr_ex,
        trap_ex
      })
  );

  //
  // Processor datapath signals
  //
  localparam
      int DATA_W = 2 + 1 + 2 + 3 + 1 + 1 + 1 + 1 + 1 + 2 + 5 + 5 + 5 + 3 + 7;

  svc_rv_pipe_data #(
      .WIDTH(DATA_W),
      .REG  (PIPELINED)
  ) pipe_data_signals (
      .clk(clk),
      .rst_n(rst_n),
      .advance(advance),
      .flush(1'b0),
      .bubble(bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i({
        alu_a_src_id,
        alu_b_src_id,
        alu_instr_id,
        res_src_id,
        jb_tgt_src_id,
        is_mc_id,
        is_m_id,
        is_csr_id,
        is_ebreak_id,
        instr_invalid_id ? TRAP_INSTR_INVALID : TRAP_NONE,
        rd_id,
        rs1_id,
        rs2_id,
        funct3_id,
        funct7_id
      }),
      .data_o({
        alu_a_src_ex,
        alu_b_src_ex,
        alu_instr_ex,
        res_src_ex,
        jb_tgt_src_ex,
        is_mc_ex,
        is_m_ex,
        is_csr_ex,
        is_ebreak_ex,
        trap_code_ex,
        rd_ex,
        rs1_ex,
        rs2_ex,
        funct3_ex,
        funct7_ex
      })
  );

  // Forwarded register data: rs1_data, rs2_data
  //
  // When pipelined, use forwarded register values; otherwise use raw regfile.
  // Forwarded values can change during backpressure as downstream stages
  // progress, so stability check is disabled.
  //
  localparam int FWD_DATA_W = 2 * XLEN;

  (* max_fanout = 32 *) logic [FWD_DATA_W-1:0] fwd_data_id;

  if (PIPELINED != 0) begin : g_fwd
    assign fwd_data_id = {fwd_rs1_id, fwd_rs2_id};
  end else begin : g_fwd_raw
    assign fwd_data_id = {rs1_data_id, rs2_data_id};
    `SVC_UNUSED({fwd_rs1_id, fwd_rs2_id});
  end

  svc_rv_pipe_data #(
      .WIDTH(FWD_DATA_W),
      .REG  (PIPELINED)
  ) pipe_fwd_data (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (1'b0),
      .bubble (bubble),
`ifdef FORMAL
      // see note above
      .s_valid(s_valid),
      .s_ready(1'b1),
`endif
      .data_i (fwd_data_id),
      .data_o ({rs1_data_ex, rs2_data_ex})
  );

  //
  // Immediate and PC values: imm, pc, pc_plus4
  //
  localparam int IMM_PC_W = 3 * XLEN;

  svc_rv_pipe_data #(
      .WIDTH(IMM_PC_W),
      .REG  (PIPELINED)
  ) pipe_imm_pc (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (1'b0),
      .bubble (bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i ({imm_id, pc_id, pc_plus4_id}),
      .data_o ({imm_ex, pc_ex, pc_plus4_ex})
  );

  //
  // Instruction register: garbage OK when invalid
  //
  svc_rv_pipe_data #(
      .WIDTH(32),
      .REG  (PIPELINED)
  ) pipe_instr (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (1'b0),
      .bubble (bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i (instr_id),
      .data_o (instr_ex)
  );

  //
  // Branch prediction signals
  //
  // When pipelined with BPRED, capture predictions that need to be preserved
  // across flush/bubble for misprediction recovery. Otherwise, pass through 0.
  //
  logic [XLEN-1:0] final_pred_tgt_id;
  logic            final_bpred_taken_id;

  if (PIPELINED != 0 && BPRED != 0) begin : g_bpred_pipe
    //
    // RAS prediction signal: valid when RAS has a target and instruction is JALR
    //
    logic ras_pred_taken_id;
    assign ras_pred_taken_id = ras_valid_id && is_jalr_id;

    //
    // Final predicted target: RAS > BTB > static (matches bpred module priority)
    //
    assign final_pred_tgt_id = ras_pred_taken_id ?
        ras_tgt_id : (btb_pred_taken_id ? btb_tgt_id : pred_tgt);
    assign final_bpred_taken_id = bpred_taken_id;
  end else begin : g_no_bpred_pipe
    assign final_pred_tgt_id    = '0;
    assign final_bpred_taken_id = 1'b0;

    `SVC_UNUSED({bpred_taken_id, btb_tgt_id, ras_valid_id, ras_tgt_id});
  end

  svc_rv_pipe_data #(
      .WIDTH     (1),
      .REG       (PIPELINED),
      .FLUSH_REG (1),
      .BUBBLE_REG(1)
  ) pipe_bpred_taken (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (flush),
      .bubble (bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i (final_bpred_taken_id),
      .data_o (bpred_taken_ex)
  );

  svc_rv_pipe_data #(
      .WIDTH    (XLEN),
      .REG      (PIPELINED),
      .FLUSH_REG(1)
  ) pipe_pred_tgt (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (flush),
      .bubble (bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(!stall_id),
`endif
      .data_i (final_pred_tgt_id),
      .data_o (pred_tgt_ex)
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_ID
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
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
  // Constraint: id_ex_flush must not fire when EX has valid non-advancing data
  //
  // The hazard module (svc_rv_hazard.sv) guarantees this - it excludes
  // redir_pending_if from id_ex_flush because when redir_pending_if fires,
  // ID has a bubble (from prior if_id_flush), so there's nothing to flush.
  // Flushing would corrupt bpred_taken_ex for the valid instruction in EX.
  //
  always_comb begin
    `FASSUME(a_no_flush_when_stalled, !(m_valid && stall_id && id_ex_flush));
  end

  //
  // Input stability assumptions (stall-based flow control from IF)
  //
  // IF holds outputs stable when stalled. IF stalls when stall_pc is high:
  // stall_pc = stall_cpu || data_hazard_id || op_active_ex
  //
  // Since stall_id = stall_cpu || op_active_ex, we have:
  // stall_pc = stall_id || data_hazard_id
  //
  // When stall_pc was high (IF stalled), all IF outputs must be stable.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(stall_id || data_hazard_id)) begin
        `FASSUME(a_s_valid_stable, s_valid == $past(s_valid));
        `FASSUME(a_instr_id_stable, instr_id == $past(instr_id));
        `FASSUME(a_pc_id_stable, pc_id == $past(pc_id));
        `FASSUME(a_pc_plus4_id_stable, pc_plus4_id == $past(pc_plus4_id));

        //
        // Decoder outputs are combinational from instr_id, so stable if
        // instr_id stable. Formal tools don't propagate stability through
        // combinational logic, so we need explicit assumptions.
        //
        `FASSUME(a_alu_a_src_id_stable, alu_a_src_id == $past(alu_a_src_id));
        `FASSUME(a_alu_b_src_id_stable, alu_b_src_id == $past(alu_b_src_id));
        `FASSUME(a_alu_instr_id_stable, alu_instr_id == $past(alu_instr_id));
        `FASSUME(a_res_src_id_stable, res_src_id == $past(res_src_id));
        `FASSUME(a_jb_tgt_src_id_stable, jb_tgt_src_id == $past(jb_tgt_src_id));
        `FASSUME(a_is_mc_id_stable, is_mc_id == $past(is_mc_id));
        `FASSUME(a_is_m_id_stable, is_m_id == $past(is_m_id));
        `FASSUME(a_is_csr_id_stable, is_csr_id == $past(is_csr_id));
        `FASSUME(a_is_ebreak_id_stable, is_ebreak_id == $past(is_ebreak_id));
        `FASSUME(a_instr_invalid_id_stable, instr_invalid_id == $past(
                 instr_invalid_id));
        `FASSUME(a_rd_id_stable, rd_id == $past(rd_id));
        `FASSUME(a_rs1_id_stable, rs1_id == $past(rs1_id));
        `FASSUME(a_rs2_id_stable, rs2_id == $past(rs2_id));
        `FASSUME(a_funct3_id_stable, funct3_id == $past(funct3_id));
        `FASSUME(a_funct7_id_stable, funct7_id == $past(funct7_id));
        `FASSUME(a_imm_pc_id_stable, {imm_id, pc_id, pc_plus4_id} == $past(
                 {imm_id, pc_id, pc_plus4_id}));
      end
    end
  end

  //
  // Output stability assertions (stall-based flow control)
  //
  // When stalled with valid output data, signals must remain stable unless
  // flushed. Flush is orthogonal to flow control.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(m_valid && stall_id && !id_ex_flush)) begin
        // Valid must remain asserted until unstalled (unless flushed)
        `FASSERT(a_valid_stable, m_valid || id_ex_flush);

        //
        // Control signals must remain stable
        //
        `FASSERT(a_reg_write_stable, reg_write_ex == $past(reg_write_ex));
        `FASSERT(a_mem_read_stable, mem_read_ex == $past(mem_read_ex));
        `FASSERT(a_mem_write_stable, mem_write_ex == $past(mem_write_ex));
        `FASSERT(a_alu_a_src_stable, alu_a_src_ex == $past(alu_a_src_ex));
        `FASSERT(a_alu_b_src_stable, alu_b_src_ex == $past(alu_b_src_ex));
        `FASSERT(a_alu_instr_stable, alu_instr_ex == $past(alu_instr_ex));
        `FASSERT(a_res_src_stable, res_src_ex == $past(res_src_ex));
        `FASSERT(a_is_branch_stable, is_branch_ex == $past(is_branch_ex));
        `FASSERT(a_is_jmp_stable, is_jmp_ex == $past(is_jmp_ex));
        `FASSERT(a_jb_tgt_src_stable, jb_tgt_src_ex == $past(jb_tgt_src_ex));
        `FASSERT(a_is_mc_stable, is_mc_ex == $past(is_mc_ex));
        `FASSERT(a_is_m_stable, is_m_ex == $past(is_m_ex));
        `FASSERT(a_is_csr_stable, is_csr_ex == $past(is_csr_ex));
        `FASSERT(a_is_ebreak_stable, is_ebreak_ex == $past(is_ebreak_ex));
        `FASSERT(a_is_jal_stable, is_jal_ex == $past(is_jal_ex));
        `FASSERT(a_is_jalr_stable, is_jalr_ex == $past(is_jalr_ex));
        `FASSERT(a_trap_stable, trap_ex == $past(trap_ex));
        `FASSERT(a_trap_code_stable, trap_code_ex == $past(trap_code_ex));

        //
        // Datapath signals must remain stable
        //
        `FASSERT(a_instr_stable, instr_ex == $past(instr_ex));
        `FASSERT(a_rd_stable, rd_ex == $past(rd_ex));
        `FASSERT(a_rs1_stable, rs1_ex == $past(rs1_ex));
        `FASSERT(a_rs2_stable, rs2_ex == $past(rs2_ex));
        `FASSERT(a_funct3_stable, funct3_ex == $past(funct3_ex));
        `FASSERT(a_funct7_stable, funct7_ex == $past(funct7_ex));
        `FASSERT(a_rs1_data_stable, rs1_data_ex == $past(rs1_data_ex));
        `FASSERT(a_rs2_data_stable, rs2_data_ex == $past(rs2_data_ex));
        `FASSERT(a_imm_stable, imm_ex == $past(imm_ex));
        `FASSERT(a_pc_stable, pc_ex == $past(pc_ex));
        `FASSERT(a_pc_plus4_stable, pc_plus4_ex == $past(pc_plus4_ex));
        `FASSERT(a_pred_tgt_stable, pred_tgt_ex == $past(pred_tgt_ex));
      end
    end
  end

  //
  // Critical: bpred_taken_ex must remain stable when stalled with valid data.
  //
  // When stalled and we have a valid instruction in EX, bpred_taken_ex must
  // not change. The assumption a_no_flush_when_stalled constrains id_ex_flush
  // to not fire in this scenario.
  //
  // This catches bugs where id_ex_flush (e.g., from redir_pending_if with
  // PC_REG=1) corrupts the prediction via FLUSH_REG=1 on pipe_bpred_taken.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(m_valid && stall_id)) begin
        `FASSERT(a_bpred_taken_stable, bpred_taken_ex == $past(bpred_taken_ex));
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cover back-to-back valid transfers
      `FCOVER(c_back_to_back, $past(m_valid && !stall_id) && m_valid);

      // Cover stalled transfer (valid high, stall for a cycle)
      `FCOVER(c_stalled, $past(m_valid && stall_id) && m_valid && !stall_id);

      // Cover stalled with taken branch prediction - the scenario that
      // could corrupt bpred_taken_ex if id_ex_flush fired incorrectly
      `FCOVER(c_stall_bpred_taken, $past(m_valid && stall_id && bpred_taken_ex
              ));
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
