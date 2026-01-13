`include "svc_unit.sv"

`include "svc_axi_mem.sv"
`include "svc_axi_tgen_wr.sv"

module svc_axi_tgen_wr_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam AXI_ADDR_WIDTH = 16;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;
  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  logic                      start;
  logic                      busy;

  logic [AXI_ADDR_WIDTH-1:0] base_addr;
  logic [  AXI_ID_WIDTH-1:0] burst_id;
  logic [               7:0] burst_beats;
  logic [AXI_ADDR_WIDTH-1:0] burst_stride;
  logic [               2:0] burst_awsize;
  logic [              15:0] burst_num;

  logic                      s_axi_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr;
  logic [  AXI_ID_WIDTH-1:0] s_axi_awid;
  logic [               7:0] s_axi_awlen;
  logic [               2:0] s_axi_awsize;
  logic [               1:0] s_axi_awburst;
  logic                      s_axi_awready;

  logic                      s_axi_wvalid;
  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata;
  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb;
  logic                      s_axi_wlast;
  logic                      s_axi_wready;

  logic                      s_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] s_axi_bid;
  logic [               1:0] s_axi_bresp;
  logic                      s_axi_bready;

  svc_axi_tgen_wr #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .start(start),
      .busy (busy),

      .base_addr   (base_addr),
      .burst_id    (burst_id),
      .burst_beats (burst_beats),
      .burst_stride(burst_stride),
      .burst_awsize(burst_awsize),
      .burst_num   (burst_num),

      .m_axi_awvalid(s_axi_awvalid),
      .m_axi_awaddr (s_axi_awaddr),
      .m_axi_awid   (s_axi_awid),
      .m_axi_awlen  (s_axi_awlen),
      .m_axi_awsize (s_axi_awsize),
      .m_axi_awburst(s_axi_awburst),
      .m_axi_awready(s_axi_awready),

      .m_axi_wvalid(s_axi_wvalid),
      .m_axi_wdata (s_axi_wdata),
      .m_axi_wstrb (s_axi_wstrb),
      .m_axi_wlast (s_axi_wlast),
      .m_axi_wready(s_axi_wready),

      .m_axi_bvalid(s_axi_bvalid),
      .m_axi_bid   (s_axi_bid),
      .m_axi_bresp (s_axi_bresp),
      .m_axi_bready(s_axi_bready)
  );

  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bready (s_axi_bready),

      .s_axi_arvalid(1'b0),
      .s_axi_arid   ('0),
      .s_axi_araddr ('0),
      .s_axi_arlen  ('0),
      .s_axi_arsize ('0),
      .s_axi_arburst('0),
      .s_axi_arready(),
      .s_axi_rvalid (),
      .s_axi_rid    (),
      .s_axi_rdata  (),
      .s_axi_rresp  (),
      .s_axi_rlast  (),
      .s_axi_rready (1'b0)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      start        <= 1'b0;
      base_addr    <= 0;
      burst_id     <= 0;
      burst_beats  <= 8'd0;
      burst_stride <= 0;
      burst_awsize <= 3'b0;
      burst_num    <= 16'd0;
    end else begin
      start <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(busy);
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
    `CHECK_TRUE(s_axi_bready);
  endtask

  task automatic test_single_burst();
    base_addr    = 16'h1000;
    burst_id     = 4'h5;
    burst_beats  = 8'd4;
    burst_stride = 16'd16;
    burst_awsize = 3'b010;
    burst_num    = 16'd1;

    start        = 1'b1;
    `CHECK_WAIT_FOR(clk, s_axi_awvalid && s_axi_awready, 2);
    `CHECK_EQ(s_axi_awaddr, base_addr);
    `CHECK_EQ(s_axi_awlen, burst_beats - 1);
    `CHECK_EQ(s_axi_awsize, burst_awsize);
    `CHECK_EQ(s_axi_awburst, 2'b01);
    `CHECK_EQ(s_axi_awid, 4'h5);

    // end 1 early
    for (logic [7:0] i = 0; i < burst_beats - 1; i++) begin
      `CHECK_TRUE(s_axi_wvalid);
      `CHECK_FALSE(s_axi_wlast);
      `TICK(clk);
    end

    `CHECK_TRUE(s_axi_wvalid);
    `CHECK_TRUE(s_axi_wlast);

    `CHECK_WAIT_FOR(clk, s_axi_bvalid && s_axi_bready, 1);
    `CHECK_WAIT_FOR(clk, !busy, 5);
  endtask

  task automatic test_multiple_bursts();
    base_addr    = 16'h1000;
    burst_id     = 4'h5;
    burst_beats  = 8'd2;
    burst_stride = 16'd8;
    burst_awsize = 3'b001;
    burst_num    = 3;

    start        = 1'b1;
    for (logic [15:0] burst = 0; burst < burst_num; burst++) begin
      `CHECK_WAIT_FOR(clk, s_axi_awvalid && s_axi_awready, 2);
      `CHECK_TRUE(busy);
      `CHECK_EQ(s_axi_awaddr, base_addr + (burst * burst_stride));
      `CHECK_EQ(s_axi_awlen, burst_beats - 1);
      `CHECK_EQ(s_axi_awsize, burst_awsize);
      `CHECK_EQ(s_axi_awburst, 2'b01);
      `CHECK_EQ(s_axi_awid, 4'h5);

      // end 1 early
      for (logic [7:0] beat = 0; beat < burst_beats - 1; beat++) begin
        `CHECK_TRUE(s_axi_wvalid);
        `CHECK_FALSE(s_axi_wlast);
        `TICK(clk);
      end

      `CHECK_TRUE(s_axi_wvalid);
      `CHECK_TRUE(s_axi_wlast);

      `CHECK_WAIT_FOR(clk, s_axi_bvalid && s_axi_bready, 1);
      `CHECK_EQ(s_axi_bid, 4'h5);
      `CHECK_EQ(s_axi_bresp, 2'b00);

      // If not the last burst, we should still be busy
      if (burst < burst_num - 1) begin
        `CHECK_TRUE(busy);
      end
    end

    // After all bursts, should no longer be busy
    `CHECK_WAIT_FOR(clk, !busy, 1);

    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_tgen_wr_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_single_burst);
  `TEST_CASE(test_multiple_bursts);
  `TEST_SUITE_END();
endmodule
