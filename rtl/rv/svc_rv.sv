`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_imem.sv"
`include "svc_rv_pc.sv"
`include "svc_rv_idec.sv"

module svc_rv #(
    parameter int XLEN    = 32,
    parameter int IMEM_AW = 10,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    output logic ebreak
);
  logic [XLEN-1:0] pc;

  logic [    31:0] instr;

  //
  // Decoder signals
  //
  logic            reg_write;
  logic            mem_write;
  logic            alu_a_src;
  logic [     1:0] alu_b_src;
  logic [     1:0] alu_instr;
  logic [     1:0] res_src;
  logic [     2:0] imm_type;
  logic            is_branch;
  logic            is_jump;
  logic [     4:0] rd;
  logic [     4:0] rs1;
  logic [     4:0] rs2;
  logic [     2:0] funct3;
  logic [     6:0] funct7;
  logic [XLEN-1:0] imm_i;
  logic [XLEN-1:0] imm_s;
  logic [XLEN-1:0] imm_b;
  logic [XLEN-1:0] imm_u;
  logic [XLEN-1:0] imm_j;

  //
  // PC
  //
  svc_rv_pc #(
      .XLEN(XLEN)
  ) pc_ctrl (
      .clk  (clk),
      .rst_n(rst_n),
      .pc   (pc)
  );

  //
  // Instruction memory
  //
  svc_rv_imem #(
      .AW       (IMEM_AW),
      .INIT_FILE(IMEM_INIT)
  ) imem (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (1'b1),
      .addr (pc[IMEM_AW-1+2:2]),
      .data (instr)
  );

  //
  // Instruction decoder
  //
  svc_rv_idec #(
      .XLEN(XLEN)
  ) idec (
      .instr    (instr),
      .reg_write(reg_write),
      .mem_write(mem_write),
      .alu_a_src(alu_a_src),
      .alu_b_src(alu_b_src),
      .alu_instr(alu_instr),
      .res_src  (res_src),
      .imm_type (imm_type),
      .is_branch(is_branch),
      .is_jump  (is_jump),
      .rd       (rd),
      .rs1      (rs1),
      .rs2      (rs2),
      .funct3   (funct3),
      .funct7   (funct7),
      .imm_i    (imm_i),
      .imm_s    (imm_s),
      .imm_b    (imm_b),
      .imm_u    (imm_u),
      .imm_j    (imm_j)
  );

  assign ebreak = (instr == 32'h00100073);

  `SVC_UNUSED({pc[XLEN-1:IMEM_AW+2], pc[1:0], reg_write, mem_write, alu_a_src,
               alu_b_src, alu_instr, res_src, imm_type, is_branch, is_jump, rd,
               rs1, rs2, funct3, funct7, imm_i, imm_s, imm_b, imm_u, imm_j});


endmodule

`endif
