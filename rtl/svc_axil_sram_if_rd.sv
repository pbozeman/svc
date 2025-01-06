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

`ifdef FORMAL
  // This module gets formally verified up in the combined rd/wr interface, but
  // we set the assumptions that the sram interface we are wrapping
  // is well behaved here.

  //
  // The sram will accept a command in 0 to 3 cycles
  //
  logic [1:0] f_cmd_ready_delay;
  always @(posedge clk) begin
    if (!rst_n) begin
      f_cmd_ready_delay <= 0;
    end else begin
      if ($rose(sram_rd_cmd_valid)) begin
        f_cmd_ready_delay <= 0;
      end

      if (sram_rd_cmd_valid) begin
        if (!sram_rd_cmd_ready) begin
          f_cmd_ready_delay <= f_cmd_ready_delay + 1;
        end
      end

      if (sram_rd_resp_valid && !sram_rd_resp_ready) begin
        assume (!sram_rd_cmd_ready);
      end

      assume (f_cmd_ready_delay < 3 || sram_rd_cmd_ready);
      cover (f_cmd_ready_delay == 2 && sram_rd_cmd_ready);
      cover (f_cmd_ready_delay == 0 && sram_rd_cmd_ready);
    end
  end

  //
  // return data
  //
  logic f_resp_outstanding = 1'b0;

  always_comb begin
    assume (sram_rd_resp_valid == f_resp_outstanding);
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      f_resp_outstanding <= 0;
    end else begin
      if (!f_resp_outstanding) begin
        f_resp_outstanding <= sram_rd_cmd_valid && sram_rd_cmd_ready;
      end else begin
        if (sram_rd_cmd_valid && sram_rd_cmd_ready) begin
          assert (!sram_rd_resp_valid || sram_rd_resp_ready);
        end

        if (sram_rd_resp_valid && sram_rd_resp_ready) begin
          f_resp_outstanding <= sram_rd_cmd_valid && sram_rd_cmd_ready;
        end
      end
    end
  end

  //
  // the response data will be consistent until the manager reads it
  //
  always @(posedge clk) begin
    if (f_resp_outstanding && $past(f_resp_outstanding)) begin
      assume ($stable(sram_rd_resp_data));
    end
  end
`endif

endmodule
`endif
