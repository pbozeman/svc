`include "svc_unit.sv"
`include "svc_axil_invalid_rd.sv"

module svc_axil_invalid_rd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam AXIL_ADDR_WIDTH = 8;
  localparam AXIL_DATA_WIDTH = 32;

  logic                       s_axil_arvalid;
  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr;
  logic                       s_axil_arready;

  logic                       s_axil_rvalid;
  logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata;
  logic [                1:0] s_axil_rresp;
  logic                       s_axil_rready;

  svc_axil_invalid_rd #(
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arready(s_axil_arready),

      .s_axil_rvalid(s_axil_rvalid),
      .s_axil_rdata (s_axil_rdata),
      .s_axil_rresp (s_axil_rresp),
      .s_axil_rready(s_axil_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      s_axil_arvalid <= 1'b0;
      s_axil_araddr  <= '0;
      s_axil_rready  <= 1'b0;
    end else begin
      s_axil_arvalid <= s_axil_arvalid && !s_axil_arready;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(s_axil_arready);
    `CHECK_FALSE(s_axil_rvalid);
  endtask

  task automatic test_read_reject();
    for (int i = 0; i < 4; i++) begin
      s_axil_arvalid = 1'b1;
      s_axil_araddr  = 8'(i);
      s_axil_rready  = 1'b1;
      `CHECK_WAIT_FOR(clk, s_axil_rvalid && s_axil_rready, 2);
      `CHECK_EQ(s_axil_rresp, 2'b11);
      `CHECK_EQ(s_axil_rdata, 32'h0);
      `TICK(clk);
      `CHECK_FALSE(s_axil_rvalid);
    end
  endtask

  task automatic test_read_backpressure();
    s_axil_arvalid = 1'b1;
    s_axil_araddr  = 8'h42;
    s_axil_rready  = 1'b0;
    `CHECK_WAIT_FOR(clk, s_axil_rvalid, 2);
    `CHECK_EQ(s_axil_rresp, 2'b11);
    for (int i = 0; i < 4; i++) begin
      `TICK(clk);
      `CHECK_TRUE(s_axil_rvalid);
      `CHECK_EQ(s_axil_rresp, 2'b11);
    end
    s_axil_rready = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(s_axil_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_invalid_rd_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_read_reject);
  `TEST_CASE(test_read_backpressure);
  `TEST_SUITE_END();
endmodule
