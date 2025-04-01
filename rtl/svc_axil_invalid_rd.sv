`ifndef SVC_AXIL_INVALID_RD_SV
`define SVC_AXIL_INVALID_RD_SV
`include "svc.sv"
`include "svc_unused.sv"
//
// AXIL subordinate that returns errors on read
//
// It's optimized for low resource usage, not throughput.
//
module svc_axil_invalid_rd #(
    parameter AXIL_ADDR_WIDTH = 8,
    parameter AXIL_DATA_WIDTH = 16
) (
    input logic clk,
    input logic rst_n,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,

    output logic                       s_axil_rvalid,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    input  logic                       s_axil_rready
);
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axil_arready <= 1'b0;
    end else begin
      s_axil_arready <= ((!s_axil_arready && s_axil_arvalid) &&
                         (!s_axil_rvalid || s_axil_rready));
    end
  end

  assign s_axil_rresp = 2'b11;
  assign s_axil_rdata = {AXIL_DATA_WIDTH{1'b0}};

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axil_rvalid <= 1'b0;
    end else begin
      s_axil_rvalid <= s_axil_rvalid && !s_axil_rready;
      if (s_axil_arvalid && s_axil_arready) begin
        s_axil_rvalid <= 1'b1;
      end
    end
  end

  `SVC_UNUSED(s_axil_araddr);
endmodule
`endif
