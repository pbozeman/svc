`ifndef SVC_AXIL_SRAM_IF_RD_SV
`define SVC_AXIL_SRAM_IF_RD_SV

`include "svc.sv"
`include "svc_unused.sv"

// This is a lightweight wrapper to convert byte based AXI-Lite AR channel
// addresses to word based addresses used by SRAM interfaces. Responses are
// also just set to success since sram doesn't have any form of error
// reporting capabilities.
module svc_axil_sram_if_rd #(
    parameter AXIL_ADDR_WIDTH = 20,
    parameter AXIL_DATA_WIDTH = 16,
    parameter LSB             = $clog2(AXIL_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXIL_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXIL_DATA_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI-Lite subordinate interface
    //
    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    //
    // SRAM interface
    //
    output logic                       sram_rd_cmd_valid,
    input  logic                       sram_rd_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr,

    input  logic                       sram_rd_resp_valid,
    output logic                       sram_rd_resp_ready,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data
);
  assign sram_rd_cmd_valid  = s_axil_arvalid;
  assign s_axil_arready     = sram_rd_cmd_ready;
  assign sram_rd_cmd_addr   = s_axil_araddr[AXIL_ADDR_WIDTH-1:LSB];

  assign s_axil_rvalid      = sram_rd_resp_valid;
  assign s_axil_rdata       = sram_rd_resp_data;
  assign sram_rd_resp_ready = s_axil_rready;

  assign s_axil_rresp       = '0;

  `SVC_UNUSED({clk, rst_n, s_axil_araddr[LSB-1:0]});

endmodule

`endif
