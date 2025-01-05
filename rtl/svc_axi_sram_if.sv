`ifndef SVC_AXI_SRAM_IF_SV
`define SVC_AXI_SRAM_IF_SV

`include "svc.sv"
`include "svc_axi_sram_if_rd.sv"
`include "svc_axi_sram_if_wr.sv"

// This is a lightweight wrapper to convert byte based AXI to an SRAM
// interface. It arbitrates between reads and writes, as the SRAM can only
// do 1 at a time. It also converts the addresses to be word rather than byte
// based. rresp and bresp are always marked as success.
module svc_axi_sram_if #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXI_STRB_WIDTH  = (AXI_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXI_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXI_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXI_STRB_WIDTH,
    parameter SRAM_META_WIDTH = AXI_ID_WIDTH
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
    output logic                       sram_cmd_valid,
    input  logic                       sram_cmd_ready,
    output logic                       sram_cmd_wr_en,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    output logic [SRAM_META_WIDTH-1:0] sram_cmd_meta,
    output logic                       sram_cmd_last,
    output logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    input  logic                       sram_resp_valid,
    output logic                       sram_resp_ready,
    input  logic [SRAM_META_WIDTH-1:0] sram_resp_meta,
    input  logic                       sram_resp_last,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data
);
  typedef enum {
    STATE_IDLE,
    STATE_READ,
    STATE_WRITE
  } state_t;

  state_t                       state;
  state_t                       state_next;

  logic                         sram_wr_cmd_valid;
  logic                         sram_wr_cmd_ready;
  logic   [SRAM_ADDR_WIDTH-1:0] sram_wr_cmd_addr;

  logic                         sram_rd_cmd_valid;
  logic                         sram_rd_cmd_ready;
  logic   [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr;
  logic   [SRAM_META_WIDTH-1:0] sram_rd_cmd_meta;
  logic                         sram_rd_cmd_last;

  svc_axi_sram_if_wr #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_sram_if_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awready(s_axi_awready),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wready (s_axi_wready),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bready (s_axi_bready),
      .s_axi_bid    (s_axi_bid),

      .sram_wr_cmd_valid(sram_wr_cmd_valid),
      .sram_wr_cmd_ready(sram_wr_cmd_ready),
      .sram_wr_cmd_addr (sram_wr_cmd_addr),
      .sram_wr_cmd_data (sram_cmd_wr_data),
      .sram_wr_cmd_strb (sram_cmd_wr_strb)
  );

  svc_axi_sram_if_rd #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_sram_if_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arready(s_axi_arready),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rready (s_axi_rready),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),

      .sram_rd_cmd_valid   (sram_rd_cmd_valid),
      .sram_rd_cmd_ready   (sram_rd_cmd_ready),
      .sram_rd_cmd_addr    (sram_rd_cmd_addr),
      .sram_rd_cmd_meta    (sram_rd_cmd_meta),
      .sram_rd_cmd_last    (sram_rd_cmd_last),
      .sram_rd_resp_valid  (sram_resp_valid),
      .sram_rd_resp_ready  (sram_resp_ready),
      .sram_rd_resp_meta   (sram_resp_meta),
      .sram_rd_resp_last   (sram_resp_last),
      .sram_rd_resp_rd_data(sram_resp_rd_data)
  );

  //
  // State machine
  //
  // Note the ordering of the read/write checks. They ensure fairness.
  //
  always_comb begin
    state_next = state;

    case (state)
      STATE_IDLE: begin
        if (sram_rd_cmd_valid) begin
          state_next = STATE_READ;
        end else if (sram_wr_cmd_valid) begin
          state_next = STATE_WRITE;
        end
      end

      STATE_READ: begin
        if (sram_resp_valid && sram_resp_ready && sram_resp_last) begin
          if (sram_wr_cmd_valid) begin
            state_next = STATE_WRITE;
          end else if (sram_rd_cmd_valid) begin
            state_next = STATE_READ;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_WRITE: begin
        if (s_axi_bvalid && s_axi_bready) begin
          if (sram_rd_cmd_valid) begin
            state_next = STATE_READ;
          end else if (sram_wr_cmd_valid) begin
            state_next = STATE_WRITE;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Mux the signals
  //
  always_comb begin
    sram_cmd_valid    = 1'b0;
    sram_cmd_addr     = '0;
    sram_cmd_wr_en    = 1'b0;

    sram_cmd_meta     = '0;
    sram_cmd_last     = 1'b0;

    sram_rd_cmd_ready = 1'b0;
    sram_wr_cmd_ready = 1'b0;

    case (state_next)
      STATE_READ: begin
        sram_cmd_valid    = sram_rd_cmd_valid;
        sram_cmd_addr     = sram_rd_cmd_addr;
        sram_cmd_meta     = sram_rd_cmd_meta;
        sram_cmd_last     = sram_rd_cmd_last;
        sram_rd_cmd_ready = sram_cmd_ready;
      end

      STATE_WRITE: begin
        sram_cmd_valid    = sram_wr_cmd_valid;
        sram_cmd_addr     = sram_wr_cmd_addr;
        sram_cmd_wr_en    = 1'b1;
        sram_wr_cmd_ready = sram_cmd_ready;
      end
    endcase
  end
endmodule
`endif
