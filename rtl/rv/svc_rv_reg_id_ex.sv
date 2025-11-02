`ifndef SVC_RV_REG_ID_EX_SV
`define SVC_RV_REG_ID_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V pipeline register: ID to EX
//
// This register stage separates instruction decode from execution,
// enabling pipelined execution. It captures control signals, register
// values, immediates, and PC from the decode stage and presents them
// to the execute stage on the next cycle.
//
// When ID_EX_REG=0, signals are passed through combinationally instead
// of being registered, effectively disabling the pipeline stage.
//
module svc_rv_reg_id_ex #(
    parameter int XLEN      = 32,
    parameter int ID_EX_REG = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic flush,

    //
    // ID stage inputs (control signals)
    //
    input logic       reg_write_id,
    input logic       mem_write_id,
    input logic [1:0] alu_a_src_id,
    input logic       alu_b_src_id,
    input logic [1:0] alu_instr_id,
    input logic [2:0] res_src_id,
    input logic       is_branch_id,
    input logic       is_jump_id,
    input logic       jb_target_src_id,

    //
    // ID stage inputs (data)
    //
    input logic [    31:0] instr_id,
    input logic [     4:0] rd_id,
    input logic [     4:0] rs1_id,
    input logic [     4:0] rs2_id,
    input logic [     2:0] funct3_id,
    input logic [     6:0] funct7_id,
    input logic [XLEN-1:0] rs1_data_id,
    input logic [XLEN-1:0] rs2_data_id,
    input logic [XLEN-1:0] imm_id,
    input logic [XLEN-1:0] pc_id,
    input logic [XLEN-1:0] pc_plus4_id,

    //
    // ID stage inputs (branch partial comparisons)
    //
    input logic rs_eq_lo_id,
    input logic rs_lt_u_lo_id,
    input logic rs_lt_s_lo_id,

    //
    // EX stage outputs (control signals)
    //
    output logic       reg_write_ex,
    output logic       mem_write_ex,
    output logic [1:0] alu_a_src_ex,
    output logic       alu_b_src_ex,
    output logic [1:0] alu_instr_ex,
    output logic [2:0] res_src_ex,
    output logic       is_branch_ex,
    output logic       is_jump_ex,
    output logic       jb_target_src_ex,

    //
    // EX stage outputs (data)
    //
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

    //
    // EX stage outputs (branch partial comparisons)
    //
    output logic rs_eq_lo_ex,
    output logic rs_lt_u_lo_ex,
    output logic rs_lt_s_lo_ex
);
  `include "svc_rv_defs.svh"

  if (ID_EX_REG != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n || flush) begin
        reg_write_ex     <= '0;
        mem_write_ex     <= '0;
        alu_a_src_ex     <= '0;
        alu_b_src_ex     <= '0;
        alu_instr_ex     <= '0;
        res_src_ex       <= '0;
        is_branch_ex     <= '0;
        is_jump_ex       <= '0;
        jb_target_src_ex <= '0;
        instr_ex         <= 32'h00000013;
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
        rs_eq_lo_ex      <= '0;
        rs_lt_u_lo_ex    <= '0;
        rs_lt_s_lo_ex    <= '0;
      end else begin
        reg_write_ex     <= reg_write_id;
        mem_write_ex     <= mem_write_id;
        alu_a_src_ex     <= alu_a_src_id;
        alu_b_src_ex     <= alu_b_src_id;
        alu_instr_ex     <= alu_instr_id;
        res_src_ex       <= res_src_id;
        is_branch_ex     <= is_branch_id;
        is_jump_ex       <= is_jump_id;
        jb_target_src_ex <= jb_target_src_id;
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
        rs_eq_lo_ex      <= rs_eq_lo_id;
        rs_lt_u_lo_ex    <= rs_lt_u_lo_id;
        rs_lt_s_lo_ex    <= rs_lt_s_lo_id;
      end
    end
  end else begin : g_passthrough
    assign reg_write_ex     = reg_write_id;
    assign mem_write_ex     = mem_write_id;
    assign alu_a_src_ex     = alu_a_src_id;
    assign alu_b_src_ex     = alu_b_src_id;
    assign alu_instr_ex     = alu_instr_id;
    assign res_src_ex       = res_src_id;
    assign is_branch_ex     = is_branch_id;
    assign is_jump_ex       = is_jump_id;
    assign jb_target_src_ex = jb_target_src_id;
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
    assign rs_eq_lo_ex      = rs_eq_lo_id;
    assign rs_lt_u_lo_ex    = rs_lt_u_lo_id;
    assign rs_lt_s_lo_ex    = rs_lt_s_lo_id;

    `SVC_UNUSED({clk, rst_n, flush});
  end

endmodule

`endif
