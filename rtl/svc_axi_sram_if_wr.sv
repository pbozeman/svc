`ifndef SVC_AXI_SRAM_IF_WR_SV
`define SVC_AXI_SRAM_IF_WR_SV

`include "svc.sv"
`include "svc_unused.sv"

// This module provides AXI write channel functionality for an SRAM like
// submodule interface. Addresses are converted from byte to word, and
// bursting/iteration is managed in this module, with only single word
// ops going to the SRAM subordinate.

module svc_axi_sram_if_wr #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_STRB_WIDTH  = (AXI_DATA_WIDTH / 8),
    parameter AXI_ID_WIDTH    = 4,
    parameter LSB             = $clog2(AXI_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXI_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXI_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_awvalid,
    output logic                      s_axi_awready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    input  logic                      s_axi_wvalid,
    output logic                      s_axi_wready,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_bvalid,
    input  logic                      s_axi_bready,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,

    //
    // SRAM interface
    //
    output logic                       sram_wr_cmd_valid,
    input  logic                       sram_wr_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_wr_cmd_addr,
    output logic [SRAM_DATA_WIDTH-1:0] sram_wr_cmd_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_wr_cmd_strb
);
  typedef enum {
    STATE_IDLE,
    STATE_BURST,
    STATE_RESP
  } state_t;

  state_t                      state;
  state_t                      state_next;

  logic                        s_axi_awready_next;
  logic                        s_axi_bvalid_next;
  logic   [  AXI_ID_WIDTH-1:0] s_axi_bid_next;

  logic                        w_addr_valid;
  logic                        w_addr_valid_next;

  logic   [AXI_ADDR_WIDTH-1:0] w_addr;
  logic   [AXI_ADDR_WIDTH-1:0] w_addr_next;

  logic   [  AXI_ID_WIDTH-1:0] w_id;
  logic   [  AXI_ID_WIDTH-1:0] w_id_next;

  // TODO: drop remaining in favor of using s_axi_last
  logic   [               7:0] w_remaining;
  logic   [               7:0] w_remaining_next;

  logic   [               2:0] w_size;
  logic   [               2:0] w_size_next;

  logic   [               1:0] w_burst;
  logic   [               1:0] w_burst_next;

  logic                        w_last;
  logic                        w_last_next;

  assign s_axi_bresp       = 2'b00;
  assign s_axi_wready      = w_addr_valid && sram_wr_cmd_ready;

  assign sram_wr_cmd_valid = w_addr_valid && s_axi_wvalid;
  assign sram_wr_cmd_addr  = w_addr[AXI_ADDR_WIDTH-1:LSB];
  assign sram_wr_cmd_strb  = s_axi_wstrb;
  assign sram_wr_cmd_data  = s_axi_wdata;

  always_comb begin
    state_next         = state;

    w_addr_next        = w_addr;
    w_addr_valid_next  = w_addr_valid;
    w_id_next          = w_id;
    w_remaining_next   = w_remaining;
    w_size_next        = w_size;
    w_burst_next       = w_burst;
    w_last_next        = w_last;

    s_axi_awready_next = 1'b0;
    s_axi_bvalid_next  = s_axi_bvalid && !s_axi_bready;

    case (state)
      STATE_IDLE: begin
        s_axi_awready_next = 1'b1;

        if (s_axi_awvalid && s_axi_awready) begin
          state_next = STATE_BURST;
          s_axi_awready_next = 1'b0;

          w_addr_next = s_axi_awaddr;
          w_addr_valid_next = 1'b1;

          w_id_next = s_axi_awid;
          w_remaining_next = s_axi_awlen;
          w_size_next = (s_axi_awsize < 3'($clog2(AXI_STRB_WIDTH)) ?
                         s_axi_awsize : 3'($clog2(AXI_STRB_WIDTH)));
          w_burst_next = s_axi_awburst;
          w_last_next = s_axi_awlen == 0;
        end
      end

      STATE_BURST: begin
        if (s_axi_wvalid && s_axi_wready) begin
          if (w_burst != 2'b00) begin
            w_addr_next = w_addr + (1 << w_size);
          end
          w_remaining_next = w_remaining - 1;
          w_last_next      = w_remaining_next == 0;
          if (w_remaining > 0) begin
            w_addr_valid_next = 1'b1;
          end else begin
            w_addr_valid_next = 1'b0;
            if (!s_axi_bvalid || s_axi_bready) begin
              s_axi_bid_next     = w_id;
              s_axi_bvalid_next  = 1'b1;
              s_axi_awready_next = 1'b1;

              // TODO: It might be possible to go directly from here to
              // bursting again, removing a 1 bubble cycle between the end
              // of the burst and the acceptance of the next aw txn.
              state_next         = STATE_IDLE;
            end
          end
        end
      end

      STATE_RESP: begin
        if (!s_axi_bvalid || s_axi_bready) begin
          s_axi_bid_next     = w_id;
          s_axi_bvalid_next  = 1'b1;
          s_axi_awready_next = 1'b1;

          // TODO: see above
          state_next         = STATE_IDLE;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state         <= STATE_IDLE;

      s_axi_awready <= 1'b0;
      s_axi_bvalid  <= 1'b0;
      w_addr_valid  <= 1'b0;
    end else begin
      state         <= state_next;

      w_addr        <= w_addr_next;
      w_addr_valid  <= w_addr_valid_next;

      w_id          <= w_id_next;
      w_remaining   <= w_remaining_next;
      w_size        <= w_size_next;
      w_burst       <= w_burst_next;
      w_last        <= w_last_next;

      s_axi_awready <= s_axi_awready_next;
      s_axi_bvalid  <= s_axi_bvalid_next;
      s_axi_bid     <= s_axi_bid_next;
    end
  end

  `SVC_UNUSED({clk, rst_n, s_axi_wlast, s_axi_awaddr[LSB-1:0]});

endmodule
`endif
