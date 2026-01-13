`include "svc_unit.sv"
`include "svc_axil_invalid_wr.sv"

module svc_axil_invalid_wr_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam AXIL_ADDR_WIDTH = 8;
  localparam AXIL_DATA_WIDTH = 32;
  localparam AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8;

  logic                       s_axil_awvalid;
  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr;
  logic                       s_axil_awready;

  logic                       s_axil_wvalid;
  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata;
  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb;
  logic                       s_axil_wready;

  logic                       s_axil_bvalid;
  logic [                1:0] s_axil_bresp;
  logic                       s_axil_bready;

  svc_axil_invalid_wr #(
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
      .AXIL_STRB_WIDTH(AXIL_STRB_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awvalid(s_axil_awvalid),
      .s_axil_awaddr (s_axil_awaddr),
      .s_axil_awready(s_axil_awready),

      .s_axil_wvalid(s_axil_wvalid),
      .s_axil_wdata (s_axil_wdata),
      .s_axil_wstrb (s_axil_wstrb),
      .s_axil_wready(s_axil_wready),

      .s_axil_bvalid(s_axil_bvalid),
      .s_axil_bresp (s_axil_bresp),
      .s_axil_bready(s_axil_bready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      s_axil_awvalid <= 1'b0;
      s_axil_awaddr  <= '0;
      s_axil_wvalid  <= 1'b0;
      s_axil_wdata   <= '0;
      s_axil_wstrb   <= '0;
      s_axil_bready  <= 1'b0;
    end else begin
      s_axil_awvalid <= s_axil_awvalid && !s_axil_awready;
      s_axil_wvalid  <= s_axil_wvalid && !s_axil_wready;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(s_axil_awready);
    `CHECK_FALSE(s_axil_wready);
    `CHECK_FALSE(s_axil_bvalid);
  endtask

  task automatic test_write_reject();
    for (int i = 0; i < 4; i++) begin
      s_axil_awvalid = 1'b1;
      s_axil_awaddr  = 8'(i);
      s_axil_wvalid  = 1'b1;
      s_axil_wdata   = 32'h12345678;
      s_axil_wstrb   = 4'hF;
      s_axil_bready  = 1'b1;

      `CHECK_WAIT_FOR(clk, s_axil_bvalid && s_axil_bready, 2);
      `CHECK_EQ(s_axil_bresp, 2'b11);

      `TICK(clk);
      `CHECK_FALSE(s_axil_bvalid);
    end
  endtask

  task automatic test_write_backpressure();
    s_axil_awvalid = 1'b1;
    s_axil_awaddr  = 8'h42;
    s_axil_wvalid  = 1'b1;
    s_axil_wdata   = 32'hDEADBEEF;
    s_axil_wstrb   = 4'hF;
    s_axil_bready  = 1'b0;

    `CHECK_WAIT_FOR(clk, s_axil_bvalid, 2);
    `CHECK_EQ(s_axil_bresp, 2'b11);

    for (int i = 0; i < 4; i++) begin
      `TICK(clk);
      `CHECK_TRUE(s_axil_bvalid);
      `CHECK_EQ(s_axil_bresp, 2'b11);
    end

    s_axil_bready = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(s_axil_bvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_invalid_wr_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_write_reject);
  `TEST_CASE(test_write_backpressure);
  `TEST_SUITE_END();
endmodule
