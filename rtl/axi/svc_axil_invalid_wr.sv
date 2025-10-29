`ifndef SVC_AXIL_INVALID_WR_SV
`define SVC_AXIL_INVALID_WR_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// AXIL subordinate that returns errors on write
//
// It's optimized for low resource usage, not throupught.
//
module svc_axil_invalid_wr #(
    parameter AXIL_ADDR_WIDTH = 8,
    parameter AXIL_DATA_WIDTH = 16,
    parameter AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input  logic                       s_axil_awvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    output logic                       s_axil_awready,
    input  logic                       s_axil_wvalid,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    output logic                       s_axil_wready,
    output logic                       s_axil_bvalid,
    output logic [                1:0] s_axil_bresp,
    input  logic                       s_axil_bready
);
  logic w_ready;

  assign s_axil_awready = w_ready;
  assign s_axil_wready  = w_ready;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      w_ready <= 1'b0;
    end else begin
      w_ready <= (!w_ready && ((s_axil_awvalid && s_axil_wvalid) &&
                               (!s_axil_bvalid || s_axil_bready)));
    end
  end

  assign s_axil_bresp = 2'b11;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axil_bvalid <= 1'b0;
    end else begin
      s_axil_bvalid <= s_axil_bvalid && !s_axil_bready;

      if (s_axil_awvalid && s_axil_wvalid && w_ready) begin
        s_axil_bvalid <= 1'b1;
      end
    end
  end

  `SVC_UNUSED({s_axil_awaddr, s_axil_wdata, s_axil_wstrb});

endmodule
`endif
