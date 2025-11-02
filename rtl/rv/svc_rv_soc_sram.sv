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
    parameter int XLEN    = 32,
    parameter int IMEM_AW = 10,
    parameter int DMEM_AW = 10,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    output logic ebreak
);
  //
  // Instruction memory interface
  //
  logic [31:0] imem_araddr;
  logic        imem_arvalid;
  logic        imem_arready;
  logic [31:0] imem_rdata;
  logic        imem_rvalid;
  logic        imem_rready;

  //
  // Data memory interface
  //
  logic [31:0] dmem_awaddr;
  logic        dmem_awvalid;
  logic        dmem_awready;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;
  logic        dmem_wvalid;
  logic        dmem_wready;

  logic [31:0] dmem_araddr;
  logic        dmem_arvalid;
  logic        dmem_arready;
  logic [31:0] dmem_rdata;
  logic        dmem_rvalid;
  logic        dmem_rready;

  //
  // RISC-V core
  //
  svc_rv #(
      .XLEN   (XLEN),
      .IMEM_AW(IMEM_AW),
      .DMEM_AW(DMEM_AW)
  ) cpu (
      .clk         (clk),
      .rst_n       (rst_n),
      .imem_araddr (imem_araddr),
      .imem_arvalid(imem_arvalid),
      .imem_arready(imem_arready),
      .imem_rdata  (imem_rdata),
      .imem_rvalid (imem_rvalid),
      .imem_rready (imem_rready),
      .dmem_awaddr (dmem_awaddr),
      .dmem_awvalid(dmem_awvalid),
      .dmem_awready(dmem_awready),
      .dmem_wdata  (dmem_wdata),
      .dmem_wstrb  (dmem_wstrb),
      .dmem_wvalid (dmem_wvalid),
      .dmem_wready (dmem_wready),
      .dmem_araddr (dmem_araddr),
      .dmem_arvalid(dmem_arvalid),
      .dmem_arready(dmem_arready),
      .dmem_rdata  (dmem_rdata),
      .dmem_rvalid (dmem_rvalid),
      .dmem_rready (dmem_rready),
      .ebreak      (ebreak)
  );

  //
  // Instruction memory (SRAM)
  //
  svc_mem_sram #(
      .DW       (32),
      .AW       (IMEM_AW),
      .INIT_FILE(IMEM_INIT)
  ) imem (
      .clk    (clk),
      .rst_n  (rst_n),
      .araddr (imem_araddr),
      .arvalid(imem_arvalid),
      .arready(imem_arready),
      .rdata  (imem_rdata),
      .rvalid (imem_rvalid),
      .rready (imem_rready),
      .awaddr (32'h0),
      .awvalid(1'b0),
      .awready(),
      .wdata  (32'h0),
      .wstrb  (4'h0),
      .wvalid (1'b0),
      .wready ()
  );

  //
  // Data memory (SRAM)
  //
  svc_mem_sram #(
      .DW(32),
      .AW(DMEM_AW)
  ) dmem (
      .clk    (clk),
      .rst_n  (rst_n),
      .araddr (dmem_araddr),
      .arvalid(dmem_arvalid),
      .arready(dmem_arready),
      .rdata  (dmem_rdata),
      .rvalid (dmem_rvalid),
      .rready (dmem_rready),
      .awaddr (dmem_awaddr),
      .awvalid(dmem_awvalid),
      .awready(dmem_awready),
      .wdata  (dmem_wdata),
      .wstrb  (dmem_wstrb),
      .wvalid (dmem_wvalid),
      .wready (dmem_wready)
  );

endmodule

`endif
