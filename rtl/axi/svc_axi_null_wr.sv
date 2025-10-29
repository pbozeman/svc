`ifndef SVC_AXI_NULL_WR_SV
`define SVC_AXI_NULL_WR_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// AXI manager that does nothing. This can be used to null the input of
// a module that takes N manager inputs.
//
module svc_axi_null_wr #(
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    output logic                      m_axi_awvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,
    output logic                      m_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    input  logic                      m_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready
);
  assign m_axi_awvalid = 1'b0;
  assign m_axi_awid    = 0;
  assign m_axi_awaddr  = 0;
  assign m_axi_awlen   = 0;
  assign m_axi_awsize  = 0;
  assign m_axi_awburst = 0;
  assign m_axi_wvalid  = 1'b0;
  assign m_axi_wdata   = 0;
  assign m_axi_wstrb   = 0;
  assign m_axi_wlast   = 0;
  assign m_axi_bready  = 1'b1;

  `SVC_UNUSED({clk, rst_n, m_axi_awready, m_axi_wready, m_axi_bvalid,
               m_axi_bid, m_axi_bresp});

endmodule
`endif
