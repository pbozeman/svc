`ifndef SVC_AXI_ICE40_SRAM_SV
`define SVC_AXI_ICE40_SRAM_SV

`include "svc.sv"
`include "svc_axi_sram_if.sv"
`include "svc_ice40_sram_io_if.sv"

module svc_axi_ice40_sram #(
    parameter AXI_ADDR_WIDTH  = 4,
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
    // IO to/from the async sram chip
    //
    output logic [SRAM_ADDR_WIDTH-1:0] sram_io_addr,
`ifndef FORMAL
    inout  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`else
    input  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`endif
    output logic                       sram_io_we_n,
    output logic                       sram_io_oe_n,
    output logic                       sram_io_ce_n
);
  logic                       sram_cmd_valid;
  logic                       sram_cmd_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr;
  logic [SRAM_META_WIDTH-1:0] sram_cmd_meta;
  logic                       sram_cmd_last;
  logic                       sram_cmd_wr_en;
  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data;
  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb;
  logic                       sram_resp_valid;
  logic                       sram_resp_ready;
  logic [SRAM_META_WIDTH-1:0] sram_resp_meta;
  logic                       sram_resp_last;
  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data;

  svc_ice40_sram_io_if #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH),
      .SRAM_STRB_WIDTH(SRAM_STRB_WIDTH),
      .SRAM_META_WIDTH(SRAM_META_WIDTH)
  ) svc_ice40_sram_io_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid  (sram_cmd_valid),
      .sram_cmd_ready  (sram_cmd_ready),
      .sram_cmd_addr   (sram_cmd_addr),
      .sram_cmd_meta   (sram_cmd_meta),
      .sram_cmd_last   (sram_cmd_last),
      .sram_cmd_wr_en  (sram_cmd_wr_en),
      .sram_cmd_wr_data(sram_cmd_wr_data),
      .sram_cmd_wr_strb(sram_cmd_wr_strb),

      .sram_resp_valid  (sram_resp_valid),
      .sram_resp_ready  (sram_resp_ready),
      .sram_resp_meta   (sram_resp_meta),
      .sram_resp_last   (sram_resp_last),
      .sram_resp_rd_data(sram_resp_rd_data),

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

  svc_axi_sram_if #(
      .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH   (AXI_ID_WIDTH),
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH),
      .SRAM_STRB_WIDTH(SRAM_STRB_WIDTH),
      .SRAM_META_WIDTH(SRAM_META_WIDTH)
  ) svc_axi_sram_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awready(s_axi_awready),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wready (s_axi_wready),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bready (s_axi_bready),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),

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

      .sram_cmd_valid   (sram_cmd_valid),
      .sram_cmd_ready   (sram_cmd_ready),
      .sram_cmd_wr_en   (sram_cmd_wr_en),
      .sram_cmd_addr    (sram_cmd_addr),
      .sram_cmd_meta    (sram_cmd_meta),
      .sram_cmd_last    (sram_cmd_last),
      .sram_cmd_wr_data (sram_cmd_wr_data),
      .sram_cmd_wr_strb (sram_cmd_wr_strb),
      .sram_resp_valid  (sram_resp_valid),
      .sram_resp_ready  (sram_resp_ready),
      .sram_resp_meta   (sram_resp_meta),
      .sram_resp_last   (sram_resp_last),
      .sram_resp_rd_data(sram_resp_rd_data)
  );

`ifdef FORMAL_BUT_THIS_IS_NOT_WORKING
`ifdef ZIPCPU_PRIVATE
  logic f_past_valid;

  initial f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(*) begin
    if (!f_past_valid) begin
      assume (!rst_n);
    end
  end

  faxi_slave #(
      .C_AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .F_OPT_INITIAL   (0)
  ) faxi_slave_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      .i_axi_awvalid(s_axi_awvalid),
      .i_axi_awready(s_axi_awready),
      .i_axi_awid   (s_axi_awid),
      .i_axi_awaddr (s_axi_awaddr),
      .i_axi_awlen  (s_axi_awlen),
      .i_axi_awsize (s_axi_awsize),
      .i_axi_awburst(s_axi_awburst),
      .i_axi_awlock (1'b0),
      .i_axi_awcache('0),
      .i_axi_awprot ('0),
      .i_axi_awqos  ('0),

      // Write Data
      .i_axi_wdata (s_axi_wdata),
      .i_axi_wstrb (s_axi_wstrb),
      .i_axi_wlast (s_axi_wlast),
      .i_axi_wvalid(s_axi_wvalid),
      .i_axi_wready(s_axi_wready),

      // Write response
      .i_axi_bvalid(s_axi_bvalid),
      .i_axi_bready(s_axi_bready),
      .i_axi_bid   (s_axi_bid),
      .i_axi_bresp (s_axi_bresp),

      // Read address channel
      .i_axi_arvalid(s_axi_arvalid),
      .i_axi_arready(s_axi_arready),
      .i_axi_arid   (s_axi_arid),
      .i_axi_araddr (s_axi_araddr),
      .i_axi_arlen  (s_axi_arlen),
      .i_axi_arsize (s_axi_arsize),
      .i_axi_arburst(s_axi_arburst),
      .i_axi_arlock (1'b0),
      .i_axi_arcache('0),
      .i_axi_arprot ('0),
      .i_axi_arqos  ('0),

      // Read data return channel
      .i_axi_rvalid(s_axi_rvalid),
      .i_axi_rready(s_axi_rready),
      .i_axi_rid   (s_axi_rid),
      .i_axi_rdata (s_axi_rdata),
      .i_axi_rresp (s_axi_rresp),
      .i_axi_rlast (s_axi_rlast),

      // Induction signals
      .f_axi_awr_nbursts   (),
      .f_axi_wr_pending    (),
      .f_axi_rd_nbursts    (),
      .f_axi_rd_outstanding(),

      // wr count
      .f_axi_wr_checkid  (),
      .f_axi_wr_ckvalid  (),
      .f_axi_wrid_nbursts(),
      .f_axi_wr_addr     (),
      .f_axi_wr_incr     (),
      .f_axi_wr_burst    (),
      .f_axi_wr_size     (),
      .f_axi_wr_len      (),
      .f_axi_wr_lockd    (),

      // rd count
      .f_axi_rd_checkid(),
      .f_axi_rd_ckvalid(),
      .f_axi_rd_cklen  (),
      .f_axi_rd_ckaddr (),
      .f_axi_rd_ckincr (),
      .f_axi_rd_ckburst(),
      .f_axi_rd_cksize (),
      .f_axi_rd_ckarlen(),
      .f_axi_rd_cklockd(),

      .f_axi_rdid_nbursts          (),
      .f_axi_rdid_outstanding      (),
      .f_axi_rdid_ckign_nbursts    (),
      .f_axi_rdid_ckign_outstanding(),

      // Exclusive access handling
      .f_axi_ex_state              (),
      .f_axi_ex_checklock          (),
      .f_axi_rdid_bursts_to_lock   (),
      .f_axi_wrid_bursts_to_exwrite(),

      .f_axi_exreq_addr  (),
      .f_axi_exreq_len   (),
      .f_axi_exreq_burst (),
      .f_axi_exreq_size  (),
      .f_axi_exreq_return(),

      .i_active_lock (1'b0),
      .i_exlock_addr (),
      .i_exlock_len  (),
      .i_exlock_burst(),
      .i_exlock_size ()
  );
`endif
`endif

endmodule
`endif
