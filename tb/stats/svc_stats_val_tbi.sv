`include "svc_unit.sv"
`include "svc_stats_val.sv"

module svc_stats_val_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int WIDTH = 16;
  localparam int STAT_WIDTH = 32;
  localparam int BITS_PER_STAGE = 32;

  logic                  clr;
  logic                  en;
  logic [     WIDTH-1:0] val;
  logic [     WIDTH-1:0] min;
  logic [     WIDTH-1:0] max;
  logic [STAT_WIDTH-1:0] sum;

  svc_stats_val #(
      .WIDTH         (WIDTH),
      .STAT_WIDTH    (STAT_WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) uut (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .min(min),
      .max(max),
      .sum(sum)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b1;
      en  <= 1'b0;
      val <= '0;
    end
  end

  task automatic test_basic_operation();
    val = 16'h1234;
    en  = 1'b1;
    clr = 1'b0;

    `TICK(clk);
    `CHECK_EQ(min, 16'h1234);
    `CHECK_EQ(max, 16'h1234);
    `CHECK_EQ(sum, 32'h1234);

    val = 16'h0800;
    `TICK(clk);
    `CHECK_EQ(min, 16'h0800);
    `CHECK_EQ(max, 16'h1234);
    `CHECK_EQ(sum, 32'h1A34);

    val = 16'h2000;
    `TICK(clk);
    `CHECK_EQ(min, 16'h0800);
    `CHECK_EQ(max, 16'h2000);
    `CHECK_EQ(sum, 32'h3A34);

    clr = 1'b1;
    `TICK(clk);
    `CHECK_EQ(min, {WIDTH{1'b1}});
    `CHECK_EQ(max, '0);
    `CHECK_EQ(sum, '0);

    clr = 1'b0;
    en  = 1'b0;
    `TICK(clk);
    val = 16'h5555;
    `TICK(clk);
    `CHECK_EQ(min, {WIDTH{1'b1}});
    `CHECK_EQ(max, '0);
    `CHECK_EQ(sum, '0);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_val_tbi);
  `TEST_CASE(test_basic_operation);
  `TEST_SUITE_END();
endmodule
