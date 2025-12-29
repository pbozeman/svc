`ifndef SVC_RV_SOC_BRAM_SV
`define SVC_RV_SOC_BRAM_SV

`include "svc.sv"

`include "svc_mem_bram.sv"
`include "svc_rv.sv"

//
// RISC-V SoC with BRAM memories
//
// RISC-V core with separate instruction and data BRAMs.
// BRAMs have 1-cycle read latency (registered reads).
//
// Pipeline configuration:
// - MEM_TYPE=MEM_TYPE_BRAM: Use BRAM timing (1-cycle latency)
// - All pipeline registers enabled for fully-pipelined operation
// - FWD_REGFILE=1: Enabled to reduce hazards
//
module svc_rv_soc_bram #(
    parameter int XLEN        = 32,
    parameter int IMEM_DEPTH  = 1024,
    parameter int DMEM_DEPTH  = 1024,
    parameter int PIPELINED   = 1,
    parameter int FWD_REGFILE = 1,
    parameter int FWD         = 0,
    parameter int BPRED       = 0,
    parameter int BTB_ENABLE  = 0,
    parameter int BTB_ENTRIES = 16,
    parameter int RAS_ENABLE  = 0,
    parameter int RAS_DEPTH   = 8,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0,
    parameter int PC_REG      = 0,

    parameter logic [31:0] RESET_PC = 0,

    parameter IMEM_INIT = "",
    parameter DMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    //
    // Memory-mapped I/O interface
    //
    output logic        io_ren,
    output logic [31:0] io_raddr,
    input  logic [31:0] io_rdata,

    output logic        io_wen,
    output logic [31:0] io_waddr,
    output logic [31:0] io_wdata,
    output logic [ 3:0] io_wstrb,

`ifdef RISCV_FORMAL
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [31:0] rvfi_rd_wdata,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,
    output logic        rvfi_mem_valid,
    output logic        rvfi_mem_instr,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
`endif

    output logic ebreak,
    output logic trap
);
  localparam int IMEM_AW = $clog2(IMEM_DEPTH);
  localparam int DMEM_AW = $clog2(DMEM_DEPTH);

  //
  // Memory interface signals
  //
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;
  logic        imem_ren;

  logic        dmem_ren;
  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_wen;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  //
  // BRAM interface signals
  //
  logic        bram_ren;
  logic [31:0] bram_rdata;
  logic        bram_wen;

  //
  // Address decode signals
  //
  logic        io_sel_rd;
  logic        io_sel_rd_p1;
  logic        io_sel_wr;

  `include "svc_rv_defs.svh"

  //
  // Address decode
  //
  assign io_sel_rd = dmem_raddr[31];
  assign io_sel_wr = dmem_waddr[31];

  //
  // Register read select since we need to use it for the response mux
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      io_sel_rd_p1 <= 1'b0;
    end else if (dmem_ren) begin
      io_sel_rd_p1 <= io_sel_rd;
    end
  end

  //
  // Read path routing
  //
  assign bram_ren   = dmem_ren && !io_sel_rd;
  assign io_ren     = dmem_ren && io_sel_rd;
  assign io_raddr   = dmem_raddr;
  assign dmem_rdata = io_sel_rd_p1 ? io_rdata : bram_rdata;

  //
  // Write path routing
  //
  assign bram_wen   = dmem_wen && !io_sel_wr;
  assign io_wen     = dmem_wen && io_sel_wr;
  assign io_waddr   = dmem_waddr;
  assign io_wdata   = dmem_wdata;
  assign io_wstrb   = dmem_wstrb;

  //
  // RISC-V core
  //
  svc_rv #(
      .XLEN       (XLEN),
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (PIPELINED),
      .FWD_REGFILE(FWD_REGFILE),
      .FWD        (FWD),
      .MEM_TYPE   (MEM_TYPE_BRAM),
      .BPRED      (BPRED),
      .BTB_ENABLE (BTB_ENABLE),
      .BTB_ENTRIES(BTB_ENTRIES),
      .RAS_ENABLE (RAS_ENABLE),
      .RAS_DEPTH  (RAS_DEPTH),
      .EXT_ZMMUL  (EXT_ZMMUL),
      .EXT_M      (EXT_M),
      .PC_REG     (PC_REG),
      .RESET_PC   (RESET_PC)
  ) cpu (
      .clk  (clk),
      .rst_n(rst_n),

      .imem_ren  (imem_ren),
      .imem_raddr(imem_raddr),
      .imem_rdata(imem_rdata),

      .dmem_ren  (dmem_ren),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_wen),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),

      .dmem_stall(1'b0),
      .imem_stall(1'b0),

`ifdef RISCV_FORMAL
      .rvfi_valid    (rvfi_valid),
      .rvfi_order    (rvfi_order),
      .rvfi_insn     (rvfi_insn),
      .rvfi_pc_rdata (rvfi_pc_rdata),
      .rvfi_pc_wdata (rvfi_pc_wdata),
      .rvfi_rs1_addr (rvfi_rs1_addr),
      .rvfi_rs2_addr (rvfi_rs2_addr),
      .rvfi_rd_addr  (rvfi_rd_addr),
      .rvfi_rs1_rdata(rvfi_rs1_rdata),
      .rvfi_rs2_rdata(rvfi_rs2_rdata),
      .rvfi_rd_wdata (rvfi_rd_wdata),
      .rvfi_trap     (rvfi_trap),
      .rvfi_halt     (rvfi_halt),
      .rvfi_intr     (rvfi_intr),
      .rvfi_mode     (rvfi_mode),
      .rvfi_ixl      (rvfi_ixl),
      .rvfi_mem_valid(rvfi_mem_valid),
      .rvfi_mem_instr(rvfi_mem_instr),
      .rvfi_mem_addr (rvfi_mem_addr),
      .rvfi_mem_rmask(rvfi_mem_rmask),
      .rvfi_mem_wmask(rvfi_mem_wmask),
      .rvfi_mem_rdata(rvfi_mem_rdata),
      .rvfi_mem_wdata(rvfi_mem_wdata),
`endif

      .ebreak(ebreak),
      .trap  (trap)
  );

  //
  // Instruction memory (BRAM)
  //
  svc_mem_bram #(
      .DW         (32),
      .DEPTH      (IMEM_DEPTH),
      .INIT_FILE  (IMEM_INIT),
      .RESET_VALUE(32'h00000013)
  ) imem (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_en  (imem_ren),
      .rd_addr(imem_raddr),
      .rd_data(imem_rdata),
      .wr_addr(32'h0),
      .wr_data(32'h0),
      .wr_strb(4'h0),
      .wr_en  (1'b0)
  );

  //
  // Data memory (BRAM)
  //
  svc_mem_bram #(
      .DW       (32),
      .DEPTH    (DMEM_DEPTH),
      .INIT_FILE(DMEM_INIT)
  ) dmem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_en  (bram_ren),
      .rd_addr(dmem_raddr),
      .rd_data(bram_rdata),

      .wr_en  (bram_wen),
      .wr_addr(dmem_waddr),
      .wr_data(dmem_wdata),
      .wr_strb(dmem_wstrb)
  );

endmodule

`endif
