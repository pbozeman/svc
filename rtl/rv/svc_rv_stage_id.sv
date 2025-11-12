`ifndef SVC_RV_STAGE_ID_SV
`define SVC_RV_STAGE_ID_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_idec.sv"
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
    parameter int PIPELINED   = 0,
    parameter int FWD_REGFILE = PIPELINED,
    parameter int BPRED       = 0,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic id_ex_stall,
    input logic id_ex_flush,

    //
    // From IF stage
    //
    input logic [31:0] instr_id,
    input logic [31:0] pc_id,
    input logic [31:0] pc_plus4_id,

    //
    // Write-back from WB stage
    //
    input logic        reg_write_wb,
    input logic [ 4:0] rd_wb,
    input logic [31:0] rd_data_wb,

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
    output logic            is_jump_ex,
    output logic            jb_target_src_ex,
    output logic            is_mc_ex,
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
    output logic [XLEN-1:0] pred_target,
    output logic            pred_taken_id
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
  logic            is_jump_id;
  logic            jb_target_src_id;
  logic            is_mc_id;
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
      .is_jump      (is_jump_id),
      .jb_target_src(jb_target_src_id),
      .is_m         (),
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
  logic is_m_id;

  assign is_m_id  = (res_src_id == RES_M);
  assign is_mc_id = (EXT_M != 0) && is_m_id && funct3_id[2];

  //
  // Register File
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(FWD_REGFILE)
  ) regfile (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1_id),
      .rs1_data(rs1_data_id),
      .rs2_addr(rs2_id),
      .rs2_data(rs2_data_id),
      .rd_en   (reg_write_wb),
      .rd_addr (rd_wb),
      .rd_data (rd_data_wb)
  );

  //
  // Branch Prediction
  //
  // Static BTFNT (Backward Taken/Forward Not-Taken) prediction:
  // - Backward branches (negative immediate): predict taken
  // - Forward branches (positive immediate): predict not-taken
  // - JAL (unconditional PC-relative jump): predict taken
  //
  if (BPRED != 0) begin : g_bpred
    //
    // Prediction based on immediate sign (only for branches) and JAL
    //
    // Backward branches (negative displacement, imm[31]=1): predict taken
    // Forward branches (positive displacement, imm[31]=0): predict not-taken
    // JAL (PC-relative jump): predict taken
    // JALR (register-indirect): not predicted (wait for ALU)
    //
    assign pred_taken_id = ((is_branch_id && imm_id[XLEN-1]) ||
                            (is_jump_id && !jb_target_src_id));

    //
    // Predicted target calculation (PC-relative for branches and JAL)
    //
    assign pred_target = pc_id + imm_id;

  end else begin : g_no_bpred
    assign pred_taken_id = 1'b0;
    assign pred_target   = '0;
  end

  //
  // ID/EX Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    logic bpred_taken_id;

    assign bpred_taken_id = pred_taken_id;

    always_ff @(posedge clk) begin
      if (!rst_n || id_ex_flush) begin
        reg_write_ex     <= 1'b0;
        mem_read_ex      <= 1'b0;
        mem_write_ex     <= 1'b0;
        alu_a_src_ex     <= '0;
        alu_b_src_ex     <= 1'b0;
        alu_instr_ex     <= '0;
        res_src_ex       <= '0;
        is_branch_ex     <= 1'b0;
        is_jump_ex       <= 1'b0;
        jb_target_src_ex <= 1'b0;
        is_mc_ex         <= 1'b0;
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
        bpred_taken_ex   <= 1'b0;
      end else if (!id_ex_stall) begin
        reg_write_ex     <= reg_write_id;
        mem_read_ex      <= mem_read_id;
        mem_write_ex     <= mem_write_id;
        alu_a_src_ex     <= alu_a_src_id;
        alu_b_src_ex     <= alu_b_src_id;
        alu_instr_ex     <= alu_instr_id;
        res_src_ex       <= res_src_id;
        is_branch_ex     <= is_branch_id;
        is_jump_ex       <= is_jump_id;
        jb_target_src_ex <= jb_target_src_id;
        is_mc_ex         <= is_mc_id;
        instr_ex         <= instr_id;
        rd_ex            <= rd_id;
        rs1_ex           <= rs1_id;
        rs2_ex           <= rs2_id;
        funct3_ex        <= funct3_id;
        funct7_ex        <= funct7_id;
        rs1_data_ex      <= rs1_data_id;
        rs2_data_ex      <= rs2_data_id;
        imm_ex           <= imm_id;
        pc_ex            <= pc_id;
        pc_plus4_ex      <= pc_plus4_id;
        bpred_taken_ex   <= bpred_taken_id;
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
    assign is_jump_ex       = is_jump_id;
    assign jb_target_src_ex = jb_target_src_id;
    assign is_mc_ex         = is_mc_id;
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

    `SVC_UNUSED({id_ex_stall, id_ex_flush});
  end

endmodule

`endif
