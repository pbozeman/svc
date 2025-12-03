`ifndef SVC_RV_STAGE_ID_SV
`define SVC_RV_STAGE_ID_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_bpred_id.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_regfile.sv"
`include "svc_rv_fwd_id.sv"

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

    //
    // Hazard control
    //
    input logic id_ex_flush,

    //
    // From IF stage
    //
    input logic [    31:0] instr_id,
    input logic [    31:0] pc_id,
    input logic [    31:0] pc_plus4_id,
    input logic            btb_hit_id,
    input logic            btb_pred_taken_id,
    input logic [XLEN-1:0] btb_target_id,
    input logic            ras_valid_id,
    input logic [XLEN-1:0] ras_target_id,

    //
    // Ready/valid interface from IF stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // Write-back from WB stage
    //
    input logic        reg_write_wb,
    input logic [ 4:0] rd_wb,
    input logic [31:0] rd_data_wb,

    //
    // MEM stage forwarding inputs
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // Outputs to EX stage
    //
    output logic            reg_write_ex,
    output logic            mem_read_ex,
    output logic            mem_write_ex,
    output logic [     1:0] alu_a_src_ex,
    output logic            alu_b_src_ex,
    output logic [     1:0] alu_instr_ex,
    output logic [     2:0] res_src_ex,
    output logic            is_branch_ex,
    output logic            is_jmp_ex,
    output logic            jb_target_src_ex,
    output logic            is_mc_ex,
    output logic            is_m_ex,
    output logic            is_csr_ex,
    output logic            is_jal_ex,
    output logic            is_jalr_ex,
    output logic            trap_ex,
    output logic [     1:0] trap_code_ex,
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
    output logic [XLEN-1:0] pred_target_ex,

    //
    // Ready/valid interface to EX stage
    //
    output logic m_valid,
    input  logic m_ready,

    //
    // Outputs to hazard unit (combinational from ID stage)
    //
    output logic [4:0] rs1_id,
    output logic [4:0] rs2_id,
    output logic       rs1_used_id,
    output logic       rs2_used_id,

    //
    // Branch prediction outputs to IF stage
    //
    output logic [     1:0] pc_sel_id,
    output logic [XLEN-1:0] pred_target,
    output logic            pred_taken_id,
    output logic            is_jalr_id,

    //
    // BTB prediction inputs
    //
    input logic            btb_hit,
    input logic [XLEN-1:0] btb_target,
    input logic            btb_taken
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
  logic            jb_target_src_id;
  logic            is_m_id;
  logic            is_csr_id;
  logic            is_jal_id;
  logic            is_mc_id;
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
      .jb_target_src(jb_target_src_id),
      .is_m         (is_m_id),
      .is_csr       (is_csr_id),
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
      .rd_en   (reg_write_wb),
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
      .load_data_mem(load_data_mem),
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
      .ras_target_id    (ras_target_id),
      .pc_sel_id        (pc_sel_id),
      .pred_target      (pred_target),
      .pred_taken_id    (pred_taken_id),
      .bpred_taken_id   (bpred_taken_id)
  );

  //
  // Current BTB lookup signals unused - we use buffered signals from IF
  //
  `SVC_UNUSED({btb_hit, btb_target, btb_taken, btb_target_id});

  //
  // ID/EX Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    logic [XLEN-1:0] final_pred_target_id;

    if (BPRED != 0) begin : g_bpred_pipe
      //
      // RAS prediction signal: valid when RAS has a target and instruction is JALR
      //
      logic ras_pred_taken_id;
      assign ras_pred_taken_id = ras_valid_id && is_jalr_id;

      //
      // Final predicted target: RAS > BTB > static (matches bpred module priority)
      //
      assign final_pred_target_id = ras_pred_taken_id ?
          ras_target_id : (btb_pred_taken_id ? btb_target_id : pred_target);
    end else begin : g_no_bpred_pipe
      assign final_pred_target_id = '0;
    end

    //
    // Ready/valid interface: s_ready passes through from EX stage
    //
    assign s_ready = m_ready;

    //
    // Control signals: need reset for correct behavior
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        reg_write_ex   <= 1'b0;
        mem_read_ex    <= 1'b0;
        mem_write_ex   <= 1'b0;
        m_valid        <= 1'b0;
        is_branch_ex   <= 1'b0;
        is_jmp_ex      <= 1'b0;
        is_jal_ex      <= 1'b0;
        is_jalr_ex     <= 1'b0;
        trap_ex        <= 1'b0;
        bpred_taken_ex <= 1'b0;
      end else if (id_ex_flush) begin
        reg_write_ex   <= 1'b0;
        mem_read_ex    <= 1'b0;
        mem_write_ex   <= 1'b0;
        m_valid        <= 1'b0;
        is_branch_ex   <= 1'b0;
        is_jmp_ex      <= 1'b0;
        is_jal_ex      <= 1'b0;
        is_jalr_ex     <= 1'b0;
        trap_ex        <= 1'b0;
        //
        // Capture bpred_taken_id even during flush
        // When load-use hazards hold an instruction in ID, we need to latch its
        // prediction before if_id_stall releases and RAS/BTB buffers get overwritten
        //
        bpred_taken_ex <= bpred_taken_id;
      end else if (!m_valid || m_ready) begin
        m_valid        <= s_valid;
        reg_write_ex   <= reg_write_id;
        mem_read_ex    <= mem_read_id;
        mem_write_ex   <= mem_write_id;
        is_branch_ex   <= is_branch_id;
        is_jmp_ex      <= is_jmp_id;
        is_jal_ex      <= is_jal_id;
        is_jalr_ex     <= is_jalr_id;
        trap_ex        <= instr_invalid_id;
        bpred_taken_ex <= bpred_taken_id;
      end
    end

    //
    // Datapath registers
    //
    always_ff @(posedge clk) begin
      if (id_ex_flush) begin
        alu_a_src_ex     <= '0;
        alu_b_src_ex     <= 1'b0;
        alu_instr_ex     <= '0;
        res_src_ex       <= '0;
        jb_target_src_ex <= 1'b0;
        is_mc_ex         <= 1'b0;
        is_m_ex          <= 1'b0;
        is_csr_ex        <= 1'b0;
        trap_code_ex     <= TRAP_NONE;
        instr_ex         <= I_NOP;
        rd_ex            <= '0;
        rs1_ex           <= '0;
        rs2_ex           <= '0;
        funct3_ex        <= '0;
        funct7_ex        <= '0;
        rs1_data_ex      <= '0;
        rs2_data_ex      <= '0;
        imm_ex           <= '0;
        pc_ex            <= '0;
        pc_plus4_ex      <= '0;
        //
        // Capture pred_target_ex even during flush When load-use hazards hold
        // an instruction in ID, we need to latch its prediction before
        // if_id_stall releases and RAS/BTB buffers get overwritten
        //
        pred_target_ex   <= final_pred_target_id;
      end else if (!m_valid || m_ready) begin
        alu_a_src_ex     <= alu_a_src_id;
        alu_b_src_ex     <= alu_b_src_id;
        alu_instr_ex     <= alu_instr_id;
        res_src_ex       <= res_src_id;
        jb_target_src_ex <= jb_target_src_id;
        is_mc_ex         <= is_mc_id;
        is_m_ex          <= is_m_id;
        is_csr_ex        <= is_csr_id;
        trap_code_ex     <= instr_invalid_id ? TRAP_INSTR_INVALID : TRAP_NONE;
        instr_ex         <= instr_id;
        rd_ex            <= rd_id;
        rs1_ex           <= rs1_id;
        rs2_ex           <= rs2_id;
        funct3_ex        <= funct3_id;
        funct7_ex        <= funct7_id;
        rs1_data_ex      <= fwd_rs1_id;
        rs2_data_ex      <= fwd_rs2_id;
        imm_ex           <= imm_id;
        pc_ex            <= pc_id;
        pc_plus4_ex      <= pc_plus4_id;
        pred_target_ex   <= final_pred_target_id;
      end
    end


  end else begin : g_passthrough
    assign reg_write_ex     = reg_write_id;
    assign mem_read_ex      = mem_read_id;
    assign mem_write_ex     = mem_write_id;
    assign alu_a_src_ex     = alu_a_src_id;
    assign alu_b_src_ex     = alu_b_src_id;
    assign alu_instr_ex     = alu_instr_id;
    assign res_src_ex       = res_src_id;
    assign is_branch_ex     = is_branch_id;
    assign is_jmp_ex        = is_jmp_id;
    assign jb_target_src_ex = jb_target_src_id;
    assign is_mc_ex         = is_mc_id;
    assign is_m_ex          = is_m_id;
    assign is_csr_ex        = is_csr_id;
    assign is_jal_ex        = is_jal_id;
    assign is_jalr_ex       = is_jalr_id;
    assign trap_ex          = instr_invalid_id;
    assign trap_code_ex     = instr_invalid_id ? TRAP_INSTR_INVALID : TRAP_NONE;
    assign instr_ex         = instr_id;
    assign rd_ex            = rd_id;
    assign rs1_ex           = rs1_id;
    assign rs2_ex           = rs2_id;
    assign funct3_ex        = funct3_id;
    assign funct7_ex        = funct7_id;
    assign rs1_data_ex      = rs1_data_id;
    assign rs2_data_ex      = rs2_data_id;
    assign imm_ex           = imm_id;
    assign pc_ex            = pc_id;
    assign pc_plus4_ex      = pc_plus4_id;
    assign bpred_taken_ex   = 1'b0;
    assign pred_target_ex   = '0;
    assign m_valid          = s_valid;
    assign s_ready          = m_ready;

    // verilog_format: off
    `SVC_UNUSED({rst_n, id_ex_flush, fwd_rs1_id, fwd_rs2_id,
                 bpred_taken_id, ras_valid_id, ras_target_id, m_ready});
    // verilog_format: on
  end

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
  // m_valid/m_ready handshake assertions (output interface)
  //
  // Unlike strict AXI-style valid/ready, pipeline flush/kill is allowed to
  // drop m_valid even when m_ready is low. This is intentional - flush is
  // orthogonal to flow control and gates m_valid to create bubbles.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(m_valid && !m_ready && !id_ex_flush)) begin
        //
        // Valid must remain asserted until ready (unless flushed)
        //
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
        `FASSERT(a_jb_target_src_stable, jb_target_src_ex == $past(
                 jb_target_src_ex));
        `FASSERT(a_is_mc_stable, is_mc_ex == $past(is_mc_ex));
        `FASSERT(a_is_m_stable, is_m_ex == $past(is_m_ex));
        `FASSERT(a_is_csr_stable, is_csr_ex == $past(is_csr_ex));
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
        `FASSERT(a_bpred_taken_stable, bpred_taken_ex == $past(bpred_taken_ex));
        `FASSERT(a_pred_target_stable, pred_target_ex == $past(pred_target_ex));
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

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
