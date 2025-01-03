`ifndef SVC_AXI_SRAM_IF_RD_SV
`define SVC_AXI_SRAM_IF_RD_SV

`include "svc.sv"

// This module provides AXI read channel functionality for an SRAM like
// submodule interface. Addresses are converted from byte to word, and
// bursting/iteration is managed in this module, with only single word
// ops going to the SRAM subordinate.
module svc_axi_sram_if_rd #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter LSB             = $clog2(AXI_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXI_DATA_WIDTH,
    parameter SRAM_META_WIDTH = AXI_ID_WIDTH
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
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,

    //
    // SRAM interface
    //
    output logic                       sram_rd_cmd_valid,
    input  logic                       sram_rd_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr,
    output logic [SRAM_META_WIDTH-1:0] sram_rd_cmd_meta,
    output logic                       sram_rd_cmd_last,

    input  logic                       sram_rd_resp_valid,
    output logic                       sram_rd_resp_ready,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data,
    input  logic [SRAM_META_WIDTH-1:0] sram_rd_resp_meta,
    input  logic                       sram_rd_resp_last
);
  typedef enum {
    STATE_IDLE,
    STATE_BURST,
    STATE_RESP
  } state_t;

  state_t                      state;
  state_t                      state_next;

  logic                        s_axi_arready_next;

  logic                        r_addr_valid;
  logic                        r_addr_valid_next;

  logic   [AXI_ADDR_WIDTH-1:0] r_addr;
  logic   [AXI_ADDR_WIDTH-1:0] r_addr_next;

  logic   [  AXI_ID_WIDTH-1:0] r_id;
  logic   [  AXI_ID_WIDTH-1:0] r_id_next;

  logic   [               7:0] r_remaining;
  logic   [               7:0] r_remaining_next;

  logic   [               2:0] r_size;
  logic   [               2:0] r_size_next;

  logic   [               1:0] r_burst;
  logic   [               1:0] r_burst_next;

  logic                        r_last;
  logic                        r_last_next;

  assign s_axi_rvalid       = sram_rd_resp_valid;
  assign s_axi_rdata        = sram_rd_resp_data;
  assign s_axi_rresp        = 2'b00;
  assign s_axi_rid          = sram_rd_resp_meta;
  assign s_axi_rlast        = sram_rd_resp_last;

  assign sram_rd_cmd_valid  = r_addr_valid;
  assign sram_rd_cmd_addr   = r_addr[AXI_ADDR_WIDTH-1:LSB];
  assign sram_rd_cmd_meta   = r_id;
  assign sram_rd_cmd_last   = r_last;

  assign sram_rd_resp_ready = s_axi_rready;

  always_comb begin
    state_next         = state;

    r_addr_next        = r_addr;
    r_addr_valid_next  = r_addr_valid && !sram_rd_cmd_ready;

    r_id_next          = r_id;
    r_remaining_next   = r_remaining;
    r_size_next        = r_size;
    r_burst_next       = r_burst;
    r_last_next        = r_last;

    s_axi_arready_next = 1'b0;

    case (state)
      STATE_IDLE: begin
        s_axi_arready_next = 1'b1;

        if (s_axi_arvalid && s_axi_arready) begin
          state_next = STATE_BURST;
          s_axi_arready_next = 1'b0;

          r_addr_next = s_axi_araddr;
          r_addr_valid_next = 1'b1;

          r_id_next = s_axi_arid;
          r_remaining_next = s_axi_arlen;
          // verilog_format: off
          // TODO: format under nvim and make are doing different things with
          // these lines. Disable for now, but make them consistent.
          r_size_next = (s_axi_arsize < 3'($clog2(AXI_DATA_WIDTH / 8)) ?
                         s_axi_arsize : 3'($clog2(AXI_DATA_WIDTH / 8)));
          // verilog_format: on
          r_burst_next = s_axi_arburst;
          r_last_next = r_remaining_next == 0;
        end
      end

      STATE_BURST: begin
        if (sram_rd_cmd_valid && sram_rd_cmd_ready) begin
          if (r_burst != 2'b00) begin
            r_addr_next = r_addr + (1 << r_size);
          end
          r_remaining_next = r_remaining - 1;
          r_last_next      = r_remaining_next == 0;
          if (r_remaining > 0) begin
            r_addr_valid_next = 1'b1;
            state_next        = STATE_BURST;
          end else begin
            s_axi_arready_next = 1'b1;
            state_next         = STATE_IDLE;
          end
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state         <= STATE_IDLE;

      s_axi_arready <= 1'b0;
      r_addr_valid  <= 1'b0;
    end else begin
      state         <= state_next;

      r_addr        <= r_addr_next;
      r_addr_valid  <= r_addr_valid_next;

      r_id          <= r_id_next;
      r_remaining   <= r_remaining_next;
      r_size        <= r_size_next;
      r_burst       <= r_burst_next;
      r_last        <= r_last_next;

      s_axi_arready <= s_axi_arready_next;
    end
  end

endmodule
`endif
