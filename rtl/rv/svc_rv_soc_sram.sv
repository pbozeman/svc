`ifndef SVC_RV_SOC_SRAM_SV
`define SVC_RV_SOC_SRAM_SV

`include "svc.sv"

`include "svc_mem_sram.sv"
`include "svc_rv.sv"

//
// RISC-V SoC with SRAM memories
//
// Single-cycle RISC-V core with separate instruction and data SRAMs.
// Both memories have 0-cycle read latency (combinational reads).
//
module svc_rv_soc_sram #(
    parameter int XLEN        = 32,
    parameter int IMEM_DEPTH  = 1024,
    parameter int DMEM_DEPTH  = 1024,
    parameter int PIPELINED   = 0,
    parameter int FWD_REGFILE = PIPELINED,
    parameter int FWD         = 0,
    parameter int BPRED       = 0,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    //
    // Memory-mapped I/O interface
    //
    output logic [31:0] io_raddr,
    input  logic [31:0] io_rdata,

    output logic        io_wen,
    output logic [31:0] io_waddr,
    output logic [31:0] io_wdata,
    output logic [ 3:0] io_wstrb,

    output logic ebreak
);
  localparam int IMEM_AW = $clog2(IMEM_DEPTH);
  localparam int DMEM_AW = $clog2(DMEM_DEPTH);

  //
  // Memory interface signals
  //
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;

  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_wen;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  //
  // SRAM interface signals
  //
  logic [31:0] sram_rdata;
  logic        sram_wen;

  //
  // Address decode signals
  //
  logic        io_sel_rd;
  logic        io_sel_wr;

  `include "svc_rv_defs.svh"

  //
  // Address decode
  //
  assign io_sel_rd  = dmem_raddr[31];
  assign io_sel_wr  = dmem_waddr[31];

  //
  // Read path routing
  //
  assign io_raddr   = dmem_raddr;
  assign dmem_rdata = io_sel_rd ? io_rdata : sram_rdata;

  //
  // Write path routing
  //
  assign sram_wen   = dmem_wen && !io_sel_wr;
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
      .BPRED      (BPRED)
  ) cpu (
      .clk  (clk),
      .rst_n(rst_n),

      .imem_ren  (),
      .imem_raddr(imem_raddr),
      .imem_rdata(imem_rdata),

      .dmem_ren  (),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_wen),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),

      .ebreak(ebreak)
  );

  //
  // Instruction memory (SRAM)
  //
  svc_mem_sram #(
      .DW       (32),
      .DEPTH    (IMEM_DEPTH),
      .INIT_FILE(IMEM_INIT)
  ) imem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_addr(imem_raddr),
      .rd_data(imem_rdata),

      .wr_en  (1'b0),
      .wr_addr(32'h0),
      .wr_data(32'h0),
      .wr_strb(4'h0)
  );

  //
  // Data memory (SRAM)
  //
  svc_mem_sram #(
      .DW   (32),
      .DEPTH(DMEM_DEPTH)
  ) dmem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_addr(dmem_raddr),
      .rd_data(sram_rdata),

      .wr_en  (sram_wen),
      .wr_addr(dmem_waddr),
      .wr_data(dmem_wdata),
      .wr_strb(dmem_wstrb)
  );

endmodule

`endif
