`ifndef SVC_AXIL_SRAM_IF_WR_SV
`define SVC_AXIL_SRAM_IF_WR_SV

`include "svc.sv"
`include "svc_unused.sv"

// This is a lightweight wrapper to convert byte based AXI-Lite AW channel
// addresses to word based addresses used by SRAM interfaces. The AW and
// W channels are combined into a single ready/valid signal. Responses are
// also just set to success since sram doesn't have any form of error
// reporting capabilities.
module svc_axil_sram_if_wr #(
    parameter AXIL_ADDR_WIDTH = 20,
    parameter AXIL_DATA_WIDTH = 16,
    parameter AXIL_STRB_WIDTH = (AXIL_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXIL_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXIL_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXIL_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXIL_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI-Lite subordinate interface
    //
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [                1:0] s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    //
    // SRAM interface
    //
    output logic                       sram_wr_cmd_valid,
    input  logic                       sram_wr_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_wr_cmd_addr,
    output logic [SRAM_DATA_WIDTH-1:0] sram_wr_cmd_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_wr_cmd_strb
);
  logic bvalid;
  logic bvalid_next;

  assign sram_wr_cmd_valid = (s_axil_awvalid && s_axil_wvalid);
  assign sram_wr_cmd_addr  = s_axil_awaddr[AXIL_ADDR_WIDTH-1:LSB];
  assign sram_wr_cmd_strb  = s_axil_wstrb;
  assign sram_wr_cmd_data  = s_axil_wdata;

  assign s_axil_awready    = (sram_wr_cmd_ready && sram_wr_cmd_valid);
  assign s_axil_wready     = (sram_wr_cmd_ready && sram_wr_cmd_valid);

  assign s_axil_bvalid     = bvalid;
  assign s_axil_bresp      = 2'b00;

  always_comb begin
    bvalid_next = bvalid;
    if (sram_wr_cmd_valid && sram_wr_cmd_ready) begin
      bvalid_next = 1'b1;
    end else if (s_axil_bvalid && s_axil_bready) begin
      bvalid_next = 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      bvalid <= 1'b0;
    end else begin
      bvalid <= bvalid_next;
    end
  end

  `SVC_UNUSED({clk, rst_n, s_axil_bready, s_axil_awaddr[LSB-1:0]});

endmodule
`endif
