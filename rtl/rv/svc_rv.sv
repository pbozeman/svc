`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_csr.sv"
`include "svc_rv_hazard.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_ld_fmt.sv"
`include "svc_rv_pc.sv"
`include "svc_rv_reg_ex_mem.sv"
`include "svc_rv_reg_id_ex.sv"
`include "svc_rv_reg_if_id.sv"
`include "svc_rv_reg_mem_wb.sv"
`include "svc_rv_regfile.sv"
`include "svc_rv_st_fmt.sv"

module svc_rv #(
    parameter int XLEN        = 32,
    parameter int IMEM_AW     = 10,
    parameter int DMEM_AW     = 10,
    parameter int IF_ID_REG   = 0,
    parameter int ID_EX_REG   = 0,
    parameter int EX_MEM_REG  = 0,
    parameter int MEM_WB_REG  = 0,
    parameter int REGFILE_FWD = 1
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
  localparam int PIPELINED = IF_ID_REG | ID_EX_REG | EX_MEM_REG | MEM_WB_REG;

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;

  logic [    31:0] instr;
  logic            pc_sel;

  //
  // IF/ID pipeline register signals
  //
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  //
  // ID stage signals
  //
  logic            reg_write_id;
  logic            mem_write_id;
  logic [     1:0] alu_a_src_id;
  logic            alu_b_src_id;
  logic [     1:0] alu_instr_id;
  logic [     2:0] res_src_id;
  logic [     2:0] imm_type;
  logic            is_branch_id;
  logic            is_jump_id;
  logic            jb_target_src_id;
  logic [     4:0] rd_id;
  logic [     4:0] rs1_id;
  logic [     4:0] rs2_id;
  logic [     2:0] funct3_id;
  logic [     6:0] funct7_id;
  logic            rs1_used_id;
  logic            rs2_used_id;
  logic [XLEN-1:0] imm_i;
  logic [XLEN-1:0] imm_s;
  logic [XLEN-1:0] imm_b;
  logic [XLEN-1:0] imm_u;
  logic [XLEN-1:0] imm_j;
  logic [XLEN-1:0] imm_id;
  logic [XLEN-1:0] rs1_data_id;
  logic [XLEN-1:0] rs2_data_id;
  logic            rs_eq_lo_id;
  logic            rs_lt_u_lo_id;
  logic            rs_lt_s_lo_id;

  //
  // ID/EX pipeline register signals
  //
  logic            reg_write_ex;
  logic            mem_write_ex;
  logic [     1:0] alu_a_src_ex;
  logic            alu_b_src_ex;
  logic [     1:0] alu_instr_ex;
  logic [     2:0] res_src_ex;
  logic            is_branch_ex;
  logic            is_jump_ex;
  logic            jb_target_src_ex;
  logic [    31:0] instr_ex;
  logic [     4:0] rd_ex;
  logic [     4:0] rs1_ex;
  logic [     4:0] rs2_ex;
  logic [     2:0] funct3_ex;
  logic [     6:0] funct7_ex;
  logic [XLEN-1:0] rs1_data_ex;
  logic [XLEN-1:0] rs2_data_ex;
  logic [XLEN-1:0] imm_ex;
  logic [XLEN-1:0] pc_ex;
  logic [XLEN-1:0] pc_plus4_ex;
  logic            rs_eq_lo_ex;
  logic            rs_lt_u_lo_ex;
  logic            rs_lt_s_lo_ex;

  //
  // EX stage signals
  //
  logic [     3:0] alu_op_ex;
  logic [XLEN-1:0] alu_a_ex;
  logic [XLEN-1:0] alu_b_ex;
  logic [XLEN-1:0] alu_result_ex;
  logic [XLEN-1:0] jb_target_ex;

  //
  // EX/MEM pipeline register signals
  //
  logic            reg_write_mem;
  logic            mem_write_mem;
  logic [     2:0] res_src_mem;
  logic [    31:0] instr_mem;
  logic [     4:0] rd_mem;
  logic [     2:0] funct3_mem;
  logic [XLEN-1:0] alu_result_mem;
  logic [XLEN-1:0] rs2_data_mem;
  logic [XLEN-1:0] pc_plus4_mem;
  logic [XLEN-1:0] jb_target_mem;
  logic [XLEN-1:0] csr_rdata_mem;

  //
  // MEM stage signals
  //
  logic [XLEN-1:0] dmem_rdata_ext;

  //
  // MEM/WB pipeline register signals
  //
  logic            reg_write_wb;
  logic [     2:0] res_src_wb;
  logic [    31:0] instr_wb;
  logic [     4:0] rd_wb;
  logic [XLEN-1:0] alu_result_wb;
  logic [XLEN-1:0] dmem_rdata_ext_wb;
  logic [XLEN-1:0] pc_plus4_wb;
  logic [XLEN-1:0] jb_target_wb;
  logic [XLEN-1:0] csr_rdata_wb;

  //
  // WB stage signals
  //
  logic [XLEN-1:0] rd_data;

  //
  // CSR signals
  //
  logic [XLEN-1:0] csr_rdata_ex;
  logic            instr_retired;

  //
  // Hazard control signals
  //
  logic            pc_stall;
  logic            if_id_stall;
  logic            if_id_flush;
  logic            id_ex_flush;

  //
  // Instruction retirement
  //
  // An instruction retires when it reaches WB and is not a bubble.
  // Bubbles are injected as 0 on reset. Flushed instructions become NOPs
  // (0x00000013) which also should not count as retired.
  //
  assign instr_retired = (instr_wb != 32'h0) && (instr_wb != 32'h00000013);

  //
  // PC
  //
  svc_rv_pc #(
      .XLEN(XLEN)
  ) pc_ctrl (
      .clk  (clk),
      .rst_n(rst_n),

      // hazard control
      .stall(pc_stall),

      // pc sources
      .pc_sel   (pc_sel),
      .jb_target(jb_target_ex),

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

      // hazard control
      .stall(if_id_stall),
      .flush(if_id_flush),

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
      .reg_write    (reg_write_id),
      .mem_write    (mem_write_id),
      .alu_a_src    (alu_a_src_id),
      .alu_b_src    (alu_b_src_id),
      .alu_instr    (alu_instr_id),
      .res_src      (res_src_id),
      .imm_type     (imm_type),
      .is_branch    (is_branch_id),
      .is_jump      (is_jump_id),
      .jb_target_src(jb_target_src_id),
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
  // Register File
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .REGFILE_FWD(REGFILE_FWD)
  ) regfile (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1_id),
      .rs1_data(rs1_data_id),
      .rs2_addr(rs2_id),
      .rs2_data(rs2_data_id),
      .rd_en   (reg_write_wb),
      .rd_addr (rd_wb),
      .rd_data (rd_data)
  );

  //
  // Hazard Detection Unit
  //
  // Only instantiate when pipeline registers are enabled.
  // In a single-cycle design, there are no pipeline hazards.
  //
  if (PIPELINED == 1) begin : g_hazard
    svc_rv_hazard #(
        .REGFILE_FWD(REGFILE_FWD)
    ) hazard (
        // ID stage register addresses
        .rs1_id(rs1_id),
        .rs2_id(rs2_id),

        // EX stage
        .rd_ex       (rd_ex),
        .reg_write_ex(reg_write_ex),

        // MEM stage
        .rd_mem       (rd_mem),
        .reg_write_mem(reg_write_mem),

        // WB stage
        .rd_wb       (rd_wb),
        .reg_write_wb(reg_write_wb),

        // Control flow changes
        .pc_sel(pc_sel),

        // hazard control outputs
        .pc_stall   (pc_stall),
        .if_id_stall(if_id_stall),
        .if_id_flush(if_id_flush),
        .id_ex_flush(id_ex_flush)
    );
  end else begin : g_no_hazard
    assign pc_stall    = 1'b0;
    assign if_id_stall = 1'b0;
    assign if_id_flush = 1'b0;
    assign id_ex_flush = 1'b0;
  end

  //----------------------------------------------------------------------------
  // ID/EX Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_id_ex #(
      .XLEN     (XLEN),
      .ID_EX_REG(ID_EX_REG)
  ) reg_id_ex (
      .clk  (clk),
      .rst_n(rst_n),

      // hazard control
      .flush(id_ex_flush),

      // ID stage inputs
      .reg_write_id    (reg_write_id),
      .mem_write_id    (mem_write_id),
      .alu_a_src_id    (alu_a_src_id),
      .alu_b_src_id    (alu_b_src_id),
      .alu_instr_id    (alu_instr_id),
      .res_src_id      (res_src_id),
      .is_branch_id    (is_branch_id),
      .is_jump_id      (is_jump_id),
      .jb_target_src_id(jb_target_src_id),
      .instr_id        (instr_id),
      .rd_id           (rd_id),
      .rs1_id          (rs1_id),
      .rs2_id          (rs2_id),
      .funct3_id       (funct3_id),
      .funct7_id       (funct7_id),
      .rs1_data_id     (rs1_data_id),
      .rs2_data_id     (rs2_data_id),
      .imm_id          (imm_id),
      .pc_id           (pc_id),
      .pc_plus4_id     (pc_plus4_id),
      .rs_eq_lo_id     (rs_eq_lo_id),
      .rs_lt_u_lo_id   (rs_lt_u_lo_id),
      .rs_lt_s_lo_id   (rs_lt_s_lo_id),

      // EX stage outputs
      .reg_write_ex    (reg_write_ex),
      .mem_write_ex    (mem_write_ex),
      .alu_a_src_ex    (alu_a_src_ex),
      .alu_b_src_ex    (alu_b_src_ex),
      .alu_instr_ex    (alu_instr_ex),
      .res_src_ex      (res_src_ex),
      .is_branch_ex    (is_branch_ex),
      .is_jump_ex      (is_jump_ex),
      .jb_target_src_ex(jb_target_src_ex),
      .instr_ex        (instr_ex),
      .rd_ex           (rd_ex),
      .rs1_ex          (rs1_ex),
      .rs2_ex          (rs2_ex),
      .funct3_ex       (funct3_ex),
      .funct7_ex       (funct7_ex),
      .rs1_data_ex     (rs1_data_ex),
      .rs2_data_ex     (rs2_data_ex),
      .imm_ex          (imm_ex),
      .pc_ex           (pc_ex),
      .pc_plus4_ex     (pc_plus4_ex),
      .rs_eq_lo_ex     (rs_eq_lo_ex),
      .rs_lt_u_lo_ex   (rs_lt_u_lo_ex),
      .rs_lt_s_lo_ex   (rs_lt_s_lo_ex)
  );

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
  // ALU A input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (3)
  ) mux_alu_a (
      .sel (alu_a_src_ex),
      .data({pc_ex, {XLEN{1'b0}}, rs1_data_ex}),
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
      .data({imm_ex, rs2_data_ex}),
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
  // Branch comparison (spans ID and EX stages)
  //
  // TODO: it is worth looking into making the regfile a bram interface,
  // in which case this would need to split into EX and MEM stages, adding
  // an extra cycle for branches. Once a predictor is in place, revisit this
  // and see how overall CPI is impacted and total perf from being able to
  // run at faster clocks.
  //
  logic branch_taken_ex;

  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) bcmp (
      // ID input
      .a_id(rs1_data_id),
      .b_id(rs2_data_id),

      // ID output
      .rs_eq_lo_id  (rs_eq_lo_id),
      .rs_lt_u_lo_id(rs_lt_u_lo_id),
      .rs_lt_s_lo_id(rs_lt_s_lo_id),

      // EX input
      .a_ex         (rs1_data_ex),
      .b_ex         (rs2_data_ex),
      .funct3       (funct3_ex),
      .rs_eq_lo_ex  (rs_eq_lo_ex),
      .rs_lt_u_lo_ex(rs_lt_u_lo_ex),
      .rs_lt_s_lo_ex(rs_lt_s_lo_ex),

      // EX output
      .branch_taken_ex(branch_taken_ex)
  );

  //
  // PC muxing
  //
  assign pc_sel = is_branch_ex & branch_taken_ex | is_jump_ex;

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

  //----------------------------------------------------------------------------
  // EX/MEM Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_ex_mem #(
      .XLEN      (XLEN),
      .EX_MEM_REG(EX_MEM_REG)
  ) reg_ex_mem (
      .clk  (clk),
      .rst_n(rst_n),

      // EX stage inputs
      .reg_write_ex (reg_write_ex),
      .mem_write_ex (mem_write_ex),
      .res_src_ex   (res_src_ex),
      .instr_ex     (instr_ex),
      .rd_ex        (rd_ex),
      .funct3_ex    (funct3_ex),
      .alu_result_ex(alu_result_ex),
      .rs2_data_ex  (rs2_data_ex),
      .pc_plus4_ex  (pc_plus4_ex),
      .jb_target_ex (jb_target_ex),
      .csr_rdata_ex (csr_rdata_ex),

      // MEM stage outputs
      .reg_write_mem (reg_write_mem),
      .mem_write_mem (mem_write_mem),
      .res_src_mem   (res_src_mem),
      .instr_mem     (instr_mem),
      .rd_mem        (rd_mem),
      .funct3_mem    (funct3_mem),
      .alu_result_mem(alu_result_mem),
      .rs2_data_mem  (rs2_data_mem),
      .pc_plus4_mem  (pc_plus4_mem),
      .jb_target_mem (jb_target_mem),
      .csr_rdata_mem (csr_rdata_mem)
  );

  //
  // Data memory (store formatting)
  //
  svc_rv_st_fmt #(
      .XLEN(XLEN)
  ) st_fmt (
      .data_in  (rs2_data_mem),
      .addr     (alu_result_mem[1:0]),
      .funct3   (funct3_mem),
      .mem_write(mem_write_mem),
      .data_out (dmem_wdata),
      .wstrb    (dmem_wstrb)
  );

  //
  // Data memory interface
  //
  // Write address/data channels
  //
  assign dmem_awaddr  = alu_result_mem;
  assign dmem_awvalid = mem_write_mem;
  assign dmem_wvalid  = mem_write_mem;

  //
  // Read address channel
  //
  assign dmem_araddr  = alu_result_mem;
  assign dmem_arvalid = !mem_write_mem;
  assign dmem_rready  = 1'b1;

  //
  // Load data extension
  //
  svc_rv_ld_fmt #(
      .XLEN(XLEN)
  ) ld_fmt (
      .data_in (dmem_rdata),
      .addr    (alu_result_mem[1:0]),
      .funct3  (funct3_mem),
      .data_out(dmem_rdata_ext)
  );

  //----------------------------------------------------------------------------
  // MEM/WB Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_mem_wb #(
      .XLEN      (XLEN),
      .MEM_WB_REG(MEM_WB_REG)
  ) reg_mem_wb (
      .clk  (clk),
      .rst_n(rst_n),

      // MEM stage inputs
      .reg_write_mem     (reg_write_mem),
      .res_src_mem       (res_src_mem),
      .instr_mem         (instr_mem),
      .rd_mem            (rd_mem),
      .alu_result_mem    (alu_result_mem),
      .dmem_rdata_ext_mem(dmem_rdata_ext),
      .pc_plus4_mem      (pc_plus4_mem),
      .jb_target_mem     (jb_target_mem),
      .csr_rdata_mem     (csr_rdata_mem),

      // WB stage outputs
      .reg_write_wb     (reg_write_wb),
      .res_src_wb       (res_src_wb),
      .instr_wb         (instr_wb),
      .rd_wb            (rd_wb),
      .alu_result_wb    (alu_result_wb),
      .dmem_rdata_ext_wb(dmem_rdata_ext_wb),
      .pc_plus4_wb      (pc_plus4_wb),
      .jb_target_wb     (jb_target_wb),
      .csr_rdata_wb     (csr_rdata_wb)
  );

  //
  // Result mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (5)
  ) mux_res (
      .sel(res_src_wb),
      .data({
        csr_rdata_wb,
        jb_target_wb,
        pc_plus4_wb,
        dmem_rdata_ext_wb,
        alu_result_wb
      }),
      .out(rd_data)
  );

  assign ebreak = (rst_n && instr_wb == I_EBREAK);

  `SVC_UNUSED({IMEM_AW, DMEM_AW, IF_ID_REG, ID_EX_REG, EX_MEM_REG, MEM_WB_REG,
               imem_arready, imem_rvalid, dmem_awready, dmem_wready,
               dmem_arready, dmem_rvalid, pc, pc_plus4, pc_id[1:0], pc_ex[1:0],
               funct7_id[6], funct7_id[4:0], funct7_ex[6], funct7_ex[4:0],
               rs1_ex, rs2_ex, instr_ex, alu_result_mem[1:0],
               rs1_used_id, rs2_used_id});

endmodule

`endif
