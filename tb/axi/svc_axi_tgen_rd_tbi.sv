`include "svc_unit.sv"

`include "svc_axi_mem.sv"
`include "svc_axi_tgen_rd.sv"

module svc_axi_tgen_rd_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam AXI_ADDR_WIDTH = 16;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;

  logic                      start;
  logic                      busy;

  logic [AXI_ADDR_WIDTH-1:0] base_addr;
  logic [  AXI_ID_WIDTH-1:0] burst_id;
  logic [               7:0] burst_beats;
  logic [AXI_ADDR_WIDTH-1:0] burst_stride;
  logic [               2:0] burst_arsize;
  logic [              15:0] burst_num;

  logic                      s_axi_arvalid;
  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr;
  logic [  AXI_ID_WIDTH-1:0] s_axi_arid;
  logic [               7:0] s_axi_arlen;
  logic [               2:0] s_axi_arsize;
  logic [               1:0] s_axi_arburst;
  logic                      s_axi_arready;

  logic                      s_axi_rvalid;
  logic [AXI_DATA_WIDTH-1:0] s_axi_rdata;
  logic [  AXI_ID_WIDTH-1:0] s_axi_rid;
  logic [               1:0] s_axi_rresp;
  logic                      s_axi_rlast;
  logic                      s_axi_rready;

  svc_axi_tgen_rd #(
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
      .burst_arsize(burst_arsize),
      .burst_num   (burst_num),

      .m_axi_arvalid(s_axi_arvalid),
      .m_axi_araddr (s_axi_araddr),
      .m_axi_arid   (s_axi_arid),
      .m_axi_arlen  (s_axi_arlen),
      .m_axi_arsize (s_axi_arsize),
      .m_axi_arburst(s_axi_arburst),
      .m_axi_arready(s_axi_arready),

      .m_axi_rvalid(s_axi_rvalid),
      .m_axi_rdata (s_axi_rdata),
      .m_axi_rid   (s_axi_rid),
      .m_axi_rresp (s_axi_rresp),
      .m_axi_rlast (s_axi_rlast),
      .m_axi_rready(s_axi_rready)
  );

  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
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
      .s_axi_wlast  (1'b0),
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
      start        <= 1'b0;
      base_addr    <= 0;
      burst_id     <= 0;
      burst_beats  <= 8'd0;
      burst_stride <= 0;
      burst_arsize <= 3'b0;
      burst_num    <= 16'd0;
    end else begin
      start <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(busy);
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_TRUE(s_axi_rready);
  endtask

  task automatic test_single_burst();
    base_addr    = 16'h1000;
    burst_id     = 4'h5;
    burst_beats  = 8'd4;
    burst_stride = 16'd16;
    burst_arsize = 3'b010;
    burst_num    = 16'd1;

    start        = 1'b1;
    `CHECK_WAIT_FOR(clk, s_axi_arvalid && s_axi_arready, 2);
    `CHECK_EQ(s_axi_araddr, base_addr);
    `CHECK_EQ(s_axi_arlen, burst_beats - 1);
    `CHECK_EQ(s_axi_arsize, burst_arsize);
    `CHECK_EQ(s_axi_arburst, 2'b01);
    `CHECK_EQ(s_axi_arid, 4'h5);

    // end 1 early
    for (logic [7:0] i = 0; i < burst_beats - 1; i++) begin
      `CHECK_WAIT_FOR(clk, s_axi_rvalid && s_axi_rready, 2);
      `CHECK_FALSE(s_axi_rlast);
      `CHECK_EQ(s_axi_rid, 4'h5);
      `CHECK_EQ(s_axi_rresp, 2'b00);
      `TICK(clk);
    end

    `CHECK_WAIT_FOR(clk, s_axi_rvalid && s_axi_rready, 2);
    `CHECK_TRUE(s_axi_rlast);
    `CHECK_EQ(s_axi_rid, 4'h5);
    `CHECK_EQ(s_axi_rresp, 2'b00);

    `CHECK_WAIT_FOR(clk, !busy, 5);
  endtask

  task automatic test_multiple_bursts();
    base_addr    = 16'h1000;
    burst_id     = 4'h5;
    burst_beats  = 8'd2;
    burst_stride = 16'd8;
    burst_arsize = 3'b001;
    burst_num    = 3;

    start        = 1'b1;
    for (logic [15:0] burst = 0; burst < burst_num; burst++) begin
      `CHECK_WAIT_FOR(clk, s_axi_arvalid && s_axi_arready, 2);
      `CHECK_TRUE(busy);
      `CHECK_EQ(s_axi_araddr, base_addr + (burst * burst_stride));
      `CHECK_EQ(s_axi_arlen, burst_beats - 1);
      `CHECK_EQ(s_axi_arsize, burst_arsize);
      `CHECK_EQ(s_axi_arburst, 2'b01);
      `CHECK_EQ(s_axi_arid, 4'h5);

      // end 1 early
      for (logic [7:0] beat = 0; beat < burst_beats - 1; beat++) begin
        `CHECK_WAIT_FOR(clk, s_axi_rvalid && s_axi_rready, 2);
        `CHECK_FALSE(s_axi_rlast);
        `CHECK_EQ(s_axi_rid, 4'h5);
        `CHECK_EQ(s_axi_rresp, 2'b00);
        `TICK(clk);
      end

      `CHECK_WAIT_FOR(clk, s_axi_rvalid && s_axi_rready, 2);
      `CHECK_TRUE(s_axi_rlast);
      `CHECK_EQ(s_axi_rid, 4'h5);
      `CHECK_EQ(s_axi_rresp, 2'b00);

      // If not the last burst, we should still be busy
      if (burst < burst_num - 1) begin
        `CHECK_TRUE(busy);
      end
    end

    // After all bursts, should no longer be busy
    `CHECK_WAIT_FOR(clk, !busy, 5);

    `CHECK_FALSE(s_axi_arvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_tgen_rd_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_single_burst);
  `TEST_CASE(test_multiple_bursts);
  `TEST_SUITE_END();
endmodule
