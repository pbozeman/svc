`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_imem.sv"
`include "svc_rv_pc.sv"
`include "svc_rv_regfile.sv"

// NOTE:: IMEM_REGISTERED = 1 is not supported yet. It requires
// a small hazard unit.
module svc_rv #(
    parameter int XLEN            = 32,
    parameter int IMEM_AW         = 10,
    parameter bit IMEM_REGISTERED = 0,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    output logic ebreak
);
  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;

  logic [    31:0] instr;
  logic [XLEN-1:0] jb_target;
  logic            pc_sel;

  //
  // Decoder signals
  //
  logic            reg_write;
  logic            mem_write;
  logic [     1:0] alu_a_src;
  logic            alu_b_src;
  logic [     1:0] alu_instr;
  logic [     1:0] res_src;
  logic [     2:0] imm_type;
  logic            is_branch;
  logic            is_jump;
  logic            jb_target_src;
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
  // Register file signals
  //
  logic [XLEN-1:0] rs1_data;
  logic [XLEN-1:0] rs2_data;
  logic [XLEN-1:0] rd_data;

  //
  // ALU signals
  //
  logic [     3:0] alu_op;
  logic [XLEN-1:0] alu_a;
  logic [XLEN-1:0] alu_b;
  logic [XLEN-1:0] alu_result;
  logic [XLEN-1:0] imm;

  //
  // PC
  //
  svc_rv_pc #(
      .XLEN(XLEN)
  ) pc_ctrl (
      .clk  (clk),
      .rst_n(rst_n),

      // pc sources
      .pc_sel   (pc_sel),
      .jb_target(jb_target),

      // pc output
      .pc      (pc),
      .pc_plus4(pc_plus4)
  );

  //
  // Instruction memory
  //
  svc_rv_imem #(
      .AW        (IMEM_AW),
      .REGISTERED(IMEM_REGISTERED),
      .INIT_FILE (IMEM_INIT)
  ) imem (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (1'b1),
      .addr (pc[IMEM_AW-1+2:2]),
      .data (instr)
  );

  //----------------------------------------------------------------------------
  // Instruction Decode
  //----------------------------------------------------------------------------

  svc_rv_idec #(
      .XLEN(XLEN)
  ) idec (
      .instr        (instr),
      .reg_write    (reg_write),
      .mem_write    (mem_write),
      .alu_a_src    (alu_a_src),
      .alu_b_src    (alu_b_src),
      .alu_instr    (alu_instr),
      .res_src      (res_src),
      .imm_type     (imm_type),
      .is_branch    (is_branch),
      .is_jump      (is_jump),
      .jb_target_src(jb_target_src),
      .rd           (rd),
      .rs1          (rs1),
      .rs2          (rs2),
      .funct3       (funct3),
      .funct7       (funct7),
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
      .out (imm)
  );

  //----------------------------------------------------------------------------
  // Register File
  //----------------------------------------------------------------------------

  svc_rv_regfile #(
      .XLEN(XLEN)
  ) regfile (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1),
      .rs1_data(rs1_data),
      .rs2_addr(rs2),
      .rs2_data(rs2_data),
      .rd_en   (reg_write),
      .rd_addr (rd),
      .rd_data (rd_data)
  );

  //----------------------------------------------------------------------------
  // Execution
  //----------------------------------------------------------------------------

  //
  // ALU Decoder
  //
  svc_rv_alu_dec alu_dec (
      .alu_instr(alu_instr),
      .funct3   (funct3),
      .funct7_b5(funct7[5]),
      .op_b5    (instr[5]),
      .alu_op   (alu_op)
  );

  //
  // ALU A input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (3)
  ) mux_alu_a (
      .sel (alu_a_src),
      .data({pc, {XLEN{1'b0}}, rs1_data}),
      .out (alu_a)
  );

  //
  // ALU B input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_alu_b (
      .sel (alu_b_src),
      .data({imm, rs2_data}),
      .out (alu_b)
  );

  //
  // ALU
  //
  svc_rv_alu #(
      .XLEN(XLEN)
  ) alu (
      .a     (alu_a),
      .b     (alu_b),
      .alu_op(alu_op),
      .result(alu_result)
  );

  //
  // Jump/Branch target calculation
  //
  // For JALR: Use ALU result (rs1 + imm) with LSB cleared per RISC-V spec
  // For JAL/branches: Use PC + imm from dedicated adder (no LSB clearing)
  //
  logic [XLEN-1:0] jb_target_alu;
  logic [XLEN-1:0] jb_target_pc;

  assign jb_target_alu = {alu_result[XLEN-1:1], 1'b0};
  assign jb_target_pc  = pc + imm;

  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_jb_target (
      .sel (jb_target_src),
      .data({jb_target_alu, jb_target_pc}),
      .out (jb_target)
  );

  //
  // Branch comparison
  //
  logic branch_taken;

  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) bcmp (
      .a           (rs1_data),
      .b           (rs2_data),
      .funct3      (funct3),
      .branch_taken(branch_taken)
  );

  //
  // PC muxing
  //
  assign pc_sel = is_branch & branch_taken | is_jump;

  //
  // Result mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (4)
  ) mux_res (
      .sel (res_src),
      .data({jb_target, pc_plus4, {XLEN{1'bx}}, alu_result}),
      .out (rd_data)
  );

  assign ebreak = (rst_n && instr == I_EBREAK);

  `SVC_UNUSED({pc[XLEN-1:IMEM_AW+2], pc[1:0], mem_write, funct7[6], funct7[4:0]
                });

endmodule

`endif
