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
    parameter int XLEN       = 32,
    parameter int IMEM_AW    = 10,
    parameter int DMEM_AW    = 10,
    parameter int IF_ID_REG  = 0,
    parameter int ID_EX_REG  = 0,
    parameter int EX_MEM_REG = 0,
    parameter int MEM_WB_REG = 0,

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
  logic [31:0] imem_rdata;
  logic        imem_rvalid;

  //
  // Data memory interface
  //
  logic [31:0] dmem_awaddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;
  logic        dmem_wvalid;

  logic [31:0] dmem_araddr;
  logic        dmem_arvalid;
  logic [31:0] dmem_rdata;
  logic        dmem_rvalid;

  //
  // RISC-V core
  //
  svc_rv #(
      .XLEN      (XLEN),
      .IMEM_AW   (IMEM_AW),
      .DMEM_AW   (DMEM_AW),
      .IF_ID_REG (IF_ID_REG),
      .ID_EX_REG (ID_EX_REG),
      .EX_MEM_REG(EX_MEM_REG),
      .MEM_WB_REG(MEM_WB_REG)
  ) cpu (
      .clk         (clk),
      .rst_n       (rst_n),
      .imem_araddr (imem_araddr),
      .imem_arvalid(imem_arvalid),
      .imem_arready(1'b1),
      .imem_rdata  (imem_rdata),
      .imem_rvalid (imem_rvalid),
      .imem_rready (),
      .dmem_awaddr (dmem_awaddr),
      .dmem_awvalid(),
      .dmem_awready(1'b1),
      .dmem_wdata  (dmem_wdata),
      .dmem_wstrb  (dmem_wstrb),
      .dmem_wvalid (dmem_wvalid),
      .dmem_wready (1'b1),
      .dmem_araddr (dmem_araddr),
      .dmem_arvalid(dmem_arvalid),
      .dmem_arready(1'b1),
      .dmem_rdata  (dmem_rdata),
      .dmem_rvalid (dmem_rvalid),
      .dmem_rready (),
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
      .clk          (clk),
      .rst_n        (rst_n),
      .rd_addr      (imem_araddr),
      .rd_valid     (imem_arvalid),
      .rd_data      (imem_rdata),
      .rd_data_valid(imem_rvalid),
      .wr_addr      (32'h0),
      .wr_data      (32'h0),
      .wr_strb      (4'h0),
      .wr_valid     (1'b0)
  );

  //
  // Data memory (SRAM)
  //
  svc_mem_sram #(
      .DW(32),
      .AW(DMEM_AW)
  ) dmem (
      .clk          (clk),
      .rst_n        (rst_n),
      .rd_addr      (dmem_araddr),
      .rd_valid     (dmem_arvalid),
      .rd_data      (dmem_rdata),
      .rd_data_valid(dmem_rvalid),
      .wr_addr      (dmem_awaddr),
      .wr_data      (dmem_wdata),
      .wr_strb      (dmem_wstrb),
      .wr_valid     (dmem_wvalid)
  );

endmodule

`endif
