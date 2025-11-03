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
    parameter int IMEM_AW     = 10,
    parameter int DMEM_AW     = 10,
    parameter int PIPELINED   = 0,
    parameter int REGFILE_FWD = 1,

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
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;

  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_we;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  //
  // RISC-V core
  //
  svc_rv #(
      .XLEN       (XLEN),
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (PIPELINED),
      .REGFILE_FWD(REGFILE_FWD)
  ) cpu (
      .clk  (clk),
      .rst_n(rst_n),

      .imem_ren  (),
      .imem_raddr(imem_raddr),
      .imem_rdata(imem_rdata),

      .dmem_ren  (),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_we),
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
      .AW       (IMEM_AW),
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
      .DW(32),
      .AW(DMEM_AW)
  ) dmem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_addr(dmem_raddr),
      .rd_data(dmem_rdata),

      .wr_en  (dmem_we),
      .wr_addr(dmem_waddr),
      .wr_data(dmem_wdata),
      .wr_strb(dmem_wstrb)
  );

endmodule

`endif
