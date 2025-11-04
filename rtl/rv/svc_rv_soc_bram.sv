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
    parameter int IMEM_AW     = 10,
    parameter int DMEM_AW     = 10,
    parameter int PIPELINED   = 1,
    parameter int FWD_REGFILE = 1,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    output logic ebreak
);
  //
  // Memory interface signals
  //
  logic [31:0] imem_addr;
  logic [31:0] imem_data;
  logic        imem_en;

  logic [31:0] dmem_addr;
  logic [31:0] dmem_rdata;
  logic        dmem_en;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;
  logic        dmem_we;

  `include "svc_rv_defs.svh"

  //
  // RISC-V core
  //
  svc_rv #(
      .XLEN       (XLEN),
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (PIPELINED),
      .FWD_REGFILE(FWD_REGFILE),
      .MEM_TYPE   (MEM_TYPE_BRAM)
  ) cpu (
      .clk       (clk),
      .rst_n     (rst_n),
      .imem_ren  (imem_en),
      .imem_raddr(imem_addr),
      .imem_rdata(imem_data),
      .dmem_ren  (dmem_en),
      .dmem_raddr(dmem_addr),
      .dmem_rdata(dmem_rdata),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),
      .dmem_we   (dmem_we),
      .ebreak    (ebreak)
  );

  //
  // Instruction memory (BRAM)
  //
  svc_mem_bram #(
      .DW       (32),
      .AW       (IMEM_AW),
      .INIT_FILE(IMEM_INIT)
  ) imem (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_en  (imem_en),
      .rd_addr(imem_addr),
      .rd_data(imem_data),
      .wr_addr(32'h0),
      .wr_data(32'h0),
      .wr_strb(4'h0),
      .wr_en  (1'b0)
  );

  //
  // Data memory (BRAM)
  //
  svc_mem_bram #(
      .DW(32),
      .AW(DMEM_AW)
  ) dmem (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_en  (dmem_en),
      .rd_addr(dmem_addr),
      .rd_data(dmem_rdata),
      .wr_addr(dmem_waddr),
      .wr_data(dmem_wdata),
      .wr_strb(dmem_wstrb),
      .wr_en  (dmem_we)
  );

endmodule

`endif
