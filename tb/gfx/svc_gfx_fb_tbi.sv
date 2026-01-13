`include "svc_unit.sv"

`include "svc_gfx_fb.sv"

// verilator lint_off: UNUSEDSIGNAL
module svc_gfx_fb_tbi;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;

  parameter H_WIDTH = 12;
  parameter V_WIDTH = 12;
  parameter PIXEL_WIDTH = 12;

  parameter H_VISIBLE = 128;
  parameter V_VISIBLE = 128;

  localparam WORD_SHIFT = $clog2(DW / 8);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                   s_axi_awvalid;
  logic [        IDW-1:0] s_axi_awid;
  logic [         AW-1:0] s_axi_awaddr;
  logic [            7:0] s_axi_awlen;
  logic [            2:0] s_axi_awsize;
  logic [            1:0] s_axi_awburst;
  logic                   s_axi_awready;

  logic                   s_axi_wvalid;
  logic [         DW-1:0] s_axi_wdata;
  logic [       DW/8-1:0] s_axi_wstrb;
  logic                   s_axi_wlast;
  logic                   s_axi_wready;

  logic                   s_axi_bvalid;
  logic [        IDW-1:0] s_axi_bid;
  logic [            1:0] s_axi_bresp;
  logic                   s_axi_bready;

  logic                   m_gfx_valid;
  logic [    H_WIDTH-1:0] m_gfx_x;
  logic [    V_WIDTH-1:0] m_gfx_y;
  logic [PIXEL_WIDTH-1:0] m_gfx_pixel;
  logic                   m_gfx_ready;

  logic [    H_WIDTH-1:0] h_visible = H_VISIBLE;
  logic [    V_WIDTH-1:0] v_visible = V_VISIBLE;

  svc_gfx_fb #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .PIXEL_WIDTH   (PIXEL_WIDTH),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk          (clk),
      .rst_n        (rst_n),
      .s_gfx_valid  (m_gfx_valid),
      .s_gfx_x      (m_gfx_x),
      .s_gfx_y      (m_gfx_y),
      .s_gfx_pixel  (m_gfx_pixel),
      .s_gfx_ready  (m_gfx_ready),
      .h_visible    (h_visible),
      .v_visible    (v_visible),
      .m_axi_awvalid(s_axi_awvalid),
      .m_axi_awaddr (s_axi_awaddr),
      .m_axi_awid   (s_axi_awid),
      .m_axi_awlen  (s_axi_awlen),
      .m_axi_awsize (s_axi_awsize),
      .m_axi_awburst(s_axi_awburst),
      .m_axi_awready(s_axi_awready),
      .m_axi_wvalid (s_axi_wvalid),
      .m_axi_wdata  (s_axi_wdata),
      .m_axi_wstrb  (s_axi_wstrb),
      .m_axi_wlast  (s_axi_wlast),
      .m_axi_wready (s_axi_wready),
      .m_axi_bvalid (s_axi_bvalid),
      .m_axi_bid    (s_axi_bid),
      .m_axi_bresp  (s_axi_bresp),
      .m_axi_bready (s_axi_bready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_gfx_valid   <= 1'b0;

      s_axi_awready <= 1'b1;
      s_axi_wready  <= 1'b1;
      s_axi_bvalid  <= 1'b0;
      s_axi_bresp   <= 2'b00;
      s_axi_bid     <= 0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
  endtask

  task automatic test_basic;
    m_gfx_valid = 1'b1;
    m_gfx_x     = 0;
    m_gfx_y     = 1;
    m_gfx_pixel = 12'hDAB;

    `CHECK_WAIT_FOR(clk, s_axi_awvalid, 1);
    `CHECK_EQ(s_axi_awaddr, H_VISIBLE << WORD_SHIFT);
    `CHECK_EQ(s_axi_awlen, 0);

    `CHECK_TRUE(s_axi_wvalid);
    `CHECK_EQ(s_axi_wdata, DW'(12'hDAB));
    `CHECK_EQ(s_axi_wstrb, '1);
    `CHECK_TRUE(s_axi_wlast);
  endtask

  `TEST_SUITE_BEGIN(svc_gfx_fb_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
