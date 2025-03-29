`ifndef SVC_AXI_NULL_RD_SV
`define SVC_AXI_NULL_RD_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// AXI manager that does nothing. This can be used to null the input of
// a module that takes N manager inputs.
//
module svc_axi_null_rd #(
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    output logic                      m_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready
);
  assign m_axi_arvalid = 1'b0;
  assign m_axi_arid    = 0;
  assign m_axi_araddr  = 0;
  assign m_axi_arlen   = 0;
  assign m_axi_arsize  = 0;
  assign m_axi_arburst = 0;
  assign m_axi_rready  = 1'b1;

  `SVC_UNUSED({clk, rst_n, m_axi_arready, m_axi_rvalid, m_axi_rid, m_axi_rdata,
               m_axi_rresp, m_axi_rlast});

endmodule
`endif
