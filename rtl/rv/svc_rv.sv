`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_csr.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_ld_fmt.sv"
`include "svc_rv_pc.sv"
`include "svc_rv_reg_if_id.sv"
`include "svc_rv_regfile.sv"
`include "svc_rv_st_fmt.sv"

module svc_rv #(
    parameter int XLEN      = 32,
    parameter int IMEM_AW   = 10,
    parameter int DMEM_AW   = 10,
    parameter int IF_ID_REG = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Instruction memory interface (read-only)
    //
    output logic [31:0] imem_araddr,
    output logic        imem_arvalid,
    input  logic        imem_arready,
    input  logic [31:0] imem_rdata,
    input  logic        imem_rvalid,
    output logic        imem_rready,

    //
    // Data memory interface (read/write)
    //
    output logic [31:0] dmem_awaddr,
    output logic        dmem_awvalid,
    input  logic        dmem_awready,
    output logic [31:0] dmem_wdata,
    output logic [ 3:0] dmem_wstrb,
    output logic        dmem_wvalid,
    input  logic        dmem_wready,

    output logic [31:0] dmem_araddr,
    output logic        dmem_arvalid,
    input  logic        dmem_arready,
    input  logic [31:0] dmem_rdata,
    input  logic        dmem_rvalid,
    output logic        dmem_rready,

    output logic ebreak
);
  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;

  logic [    31:0] instr;
  logic [XLEN-1:0] jb_target;
  logic            pc_sel;

  //
  // IF/ID pipeline register signals
  //
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  //
  // Decoder signals
  //
  logic            reg_write;
  logic            mem_write;
  logic [     1:0] alu_a_src;
  logic            alu_b_src;
  logic [     1:0] alu_instr;
  logic [     2:0] res_src;
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
  // Data memory signals
  //
  logic [XLEN-1:0] dmem_rdata_ext;

  //
  // CSR signals
  //
  logic [XLEN-1:0] csr_rdata;
  logic            instr_retired;

  //
  // Instruction retirement
  //
  // In this single-cycle implementation, every instruction retires every cycle.
  // In a pipelined implementation, this would be connected to pipeline commit logic.
  //
  assign instr_retired = 1'b1;

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
  // Instruction memory interface
  //
  // No hazard unit yet, so always ready to accept instruction
  //
  assign imem_araddr  = pc;
  assign imem_arvalid = 1'b1;
  assign imem_rready  = 1'b1;

  assign instr        = imem_rdata;

  //----------------------------------------------------------------------------
  // IF/ID Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_if_id #(
      .XLEN     (XLEN),
      .IF_ID_REG(IF_ID_REG)
  ) reg_if_id (
      .clk  (clk),
      .rst_n(rst_n),

      // IF signals
      .instr_if   (instr),
      .pc_if      (pc),
      .pc_plus4_if(pc_plus4),

      // ID signals
      .instr_id   (instr_id),
      .pc_id      (pc_id),
      .pc_plus4_id(pc_plus4_id)
  );

  //
  // Instruction Decode
  //
  svc_rv_idec #(
      .XLEN(XLEN)
  ) idec (
      .instr        (instr_id),
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
      .op_b5    (instr_id[5]),
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
      .data({pc_id, {XLEN{1'b0}}, rs1_data}),
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
  assign jb_target_jalr   = {alu_result[XLEN-1:1], 1'b0};

  //
  // PC-relative target: Dedicated adder for JAL and branches
  //
  assign jb_target_pc_rel = pc_id + imm;

  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_jb_target (
      .sel (jb_target_src),
      .data({jb_target_jalr, jb_target_pc_rel}),
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
  // Data memory
  //
  svc_rv_st_fmt #(
      .XLEN(XLEN)
  ) st_fmt (
      .data_in  (rs2_data),
      .addr     (alu_result[1:0]),
      .funct3   (funct3),
      .mem_write(mem_write),
      .data_out (dmem_wdata),
      .wstrb    (dmem_wstrb)
  );

  //
  // Data memory interface
  //
  // Write address/data channels
  //
  assign dmem_awaddr  = alu_result;
  assign dmem_awvalid = mem_write;
  assign dmem_wvalid  = mem_write;

  //
  // Read address channel
  //
  assign dmem_araddr  = alu_result;
  assign dmem_arvalid = !mem_write;
  assign dmem_rready  = 1'b1;

  //
  // Load data extension
  //
  svc_rv_ld_fmt #(
      .XLEN(XLEN)
  ) ld_fmt (
      .data_in (dmem_rdata),
      .addr    (alu_result[1:0]),
      .funct3  (funct3),
      .data_out(dmem_rdata_ext)
  );

  //
  // CSR (Control and Status Registers) - Zicntr
  //
  svc_rv_csr csr (
      .clk        (clk),
      .rst_n      (rst_n),
      .csr_addr   (imm_i[11:0]),
      .csr_rdata  (csr_rdata),
      .instret_inc(instr_retired)
  );

  //
  // Result mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (5)
  ) mux_res (
      .sel (res_src),
      .data({csr_rdata, jb_target, pc_plus4_id, dmem_rdata_ext, alu_result}),
      .out (rd_data)
  );


  assign ebreak = (rst_n && instr_id == I_EBREAK);

  `SVC_UNUSED({IMEM_AW, DMEM_AW, imem_arready, imem_rvalid, dmem_awready,
               dmem_wready, dmem_arready, dmem_rvalid, pc, pc_plus4,
               pc_id[1:0], funct7[6], funct7[4:0]});

endmodule

`endif
