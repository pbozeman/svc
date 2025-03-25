`include "svc_unit.sv"
`include "svc_hex_fmt.sv"

module svc_hex_fmt_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int WIDTH = 32;
  localparam int N = WIDTH / 8;

  logic [ 8*N-1:0] val;
  logic [16*N-1:0] ascii;

  svc_hex_fmt #(
      .WIDTH(WIDTH)
  ) uut (
      .val  (val),
      .ascii(ascii)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      val <= '0;
    end
  end

  task automatic check_ascii_output(string expected);
    string actual = ascii;

    for (int i = 0; i < expected.len(); i++) begin
      `CHECK_EQ(actual[i], expected[i]);
    end
  endtask

  task automatic test_reset();
    check_ascii_output("00000000");
  endtask

  task automatic test_basic_conversion();
    val = 32'h12345678;
    `TICK(clk);
    check_ascii_output("12345678");
  endtask

  task automatic test_all_chars();
    val = 32'h01234567;
    `TICK(clk);

    check_ascii_output("01234567");

    val = 32'h89ABCDEF;
    `TICK(clk);

    check_ascii_output("89ABCDEF");
  endtask

  task automatic test_trunc();
    val = 32'(16'hCAFE);
    `TICK(clk);

    check_ascii_output("0000CAFE");
  endtask

  `TEST_SUITE_BEGIN(svc_hex_fmt_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_conversion);
  `TEST_CASE(test_all_chars);
  `TEST_CASE(test_trunc);
  `TEST_SUITE_END();
endmodule
