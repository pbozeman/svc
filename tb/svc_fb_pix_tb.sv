`include "svc_unit.sv"

`include "svc_axi_mem.sv"
`include "svc_fb_pix.sv"

// verilator lint_off: UNUSEDSIGNAL
module svc_fb_pix_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;

  parameter COLOR_WIDTH = 4;
  parameter H_WIDTH = 12;
  parameter V_WIDTH = 12;

  // The fb assumes H_VISIBLE is divisible by 128
  parameter H_VISIBLE = 256;
  parameter V_VISIBLE = 3;

  parameter BURST_LATENCY = 2;
  parameter EXPECTED_BURSTS = (H_VISIBLE / 128) * V_VISIBLE;
  parameter EXPECTED_READS = ((H_VISIBLE * V_VISIBLE) -
                              (BURST_LATENCY * EXPECTED_BURSTS));

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                   s_axi_arvalid;
  logic [        IDW-1:0] s_axi_arid;
  logic [         AW-1:0] s_axi_araddr;
  logic [            7:0] s_axi_arlen;
  logic [            2:0] s_axi_arsize;
  logic [            1:0] s_axi_arburst;
  logic                   s_axi_arready;
  logic                   s_axi_rvalid;
  logic [        IDW-1:0] s_axi_rid;
  logic [         DW-1:0] s_axi_rdata;
  logic [            1:0] s_axi_rresp;
  logic                   s_axi_rlast;
  logic                   s_axi_rready;

  logic                   s_pix_valid;
  logic [COLOR_WIDTH-1:0] s_pix_red;
  logic [COLOR_WIDTH-1:0] s_pix_grn;
  logic [COLOR_WIDTH-1:0] s_pix_blu;
  logic                   s_pix_ready;

  logic [    H_WIDTH-1:0] h_visible = H_VISIBLE;
  logic [    V_WIDTH-1:0] v_visible = V_VISIBLE;

  logic [           15:0] ar_cnt;
  logic [           15:0] r_cnt;
  logic [           15:0] p_cnt;

  svc_fb_pix #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .COLOR_WIDTH   (COLOR_WIDTH),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk          (clk),
      .rst_n        (rst_n),
      .m_pix_valid  (s_pix_valid),
      .m_pix_red    (s_pix_red),
      .m_pix_grn    (s_pix_grn),
      .m_pix_blu    (s_pix_blu),
      .m_pix_ready  (s_pix_ready),
      .h_visible    (h_visible),
      .v_visible    (v_visible),
      .m_axi_arvalid(s_axi_arvalid),
      .m_axi_arid   (s_axi_arid),
      .m_axi_araddr (s_axi_araddr),
      .m_axi_arlen  (s_axi_arlen),
      .m_axi_arsize (s_axi_arsize),
      .m_axi_arburst(s_axi_arburst),
      .m_axi_arready(s_axi_arready),
      .m_axi_rvalid (s_axi_rvalid),
      .m_axi_rid    (s_axi_rid),
      .m_axi_rdata  (s_axi_rdata),
      .m_axi_rresp  (s_axi_rresp),
      .m_axi_rlast  (s_axi_rlast),
      .m_axi_rready (s_axi_rready)
  );

  // it would be nice to init the mem so that we can test the pixel returns
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) svc_axi_mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(1'b0),
      .s_axi_awid   ('0),
      .s_axi_awaddr ('0),
      .s_axi_awlen  ('0),
      .s_axi_awsize ('0),
      .s_axi_awburst('0),
      .s_axi_awready(),
      .s_axi_wvalid (1'b0),
      .s_axi_wdata  ('0),
      .s_axi_wstrb  ('0),
      .s_axi_wlast  ('0),
      .s_axi_wready (),
      .s_axi_bvalid (),
      .s_axi_bid    (),
      .s_axi_bresp  (),
      .s_axi_bready (1'b0),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arready(s_axi_arready),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),
      .s_axi_rready (s_axi_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      s_pix_ready <= 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      ar_cnt <= 0;
      r_cnt  <= 0;
      p_cnt  <= 0;
    end else begin
      if (s_axi_arvalid && s_axi_arready) begin
        ar_cnt <= ar_cnt + 1;
      end

      if (s_axi_rvalid && s_axi_rready) begin
        r_cnt <= r_cnt + 1;
      end

      if (s_pix_valid && s_pix_ready) begin
        p_cnt <= p_cnt + 1;
      end
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_arvalid);
  endtask

  task automatic test_basic;
    s_pix_ready = 1'b1;

    // This isn't the most robust testing, but it's better than nothing for
    // now. This will get more of a workout in a full gfx to vga test
    for (int i = 0; i < H_VISIBLE * V_VISIBLE; i++) begin
      `TICK(clk);
    end

    `CHECK_EQ(ar_cnt, EXPECTED_BURSTS);
    `CHECK_EQ(r_cnt, EXPECTED_READS);
    `CHECK_EQ(p_cnt, EXPECTED_READS);
  endtask

  `TEST_SUITE_BEGIN(svc_fb_pix_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
