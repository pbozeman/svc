`ifndef SVC_AXI_SRAM_IF_RD_SV
`define SVC_AXI_SRAM_IF_RD_SV

`include "svc.sv"

// This module provides AXI read channel functionality for an SRAM like
// submodule interface. Addresses are converted from byte to word, and
// bursting/iteration is managed in this module, with only single word
// ops going to the SRAM subordinate.
// verilator lint_off: UNUSEDSIGNAL
// verilator lint_off: UNDRIVEN
module svc_axi_sram_if_rd #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter LSB             = $clog2(AXI_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXI_DATA_WIDTH,
    parameter SRAM_ID_WIDTH   = AXI_ID_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_arvalid,
    output logic                      s_axi_arready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_rvalid,
    input  logic                      s_axi_rready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,

    //
    // SRAM interface
    //
    output logic                       sram_rd_cmd_valid,
    input  logic                       sram_rd_cmd_ready,
    output logic [  SRAM_ID_WIDTH-1:0] sram_rd_cmd_id,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr,

    input  logic                       sram_rd_resp_valid,
    output logic                       sram_rd_resp_ready,
    input  logic [  SRAM_ID_WIDTH-1:0] sram_rd_resp_id,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data
);
  assign s_axi_rvalid = 1'b0;

  // TODO
endmodule
`endif
