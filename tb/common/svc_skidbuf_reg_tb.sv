`include "svc_unit.sv"

`include "svc_skidbuf.sv"

module svc_skidbuf_reg_tb;
  parameter DATA_WIDTH = 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                  i_valid;
  logic                  o_ready;
  logic [DATA_WIDTH-1:0] i_data;

  logic                  o_valid;
  logic                  i_ready;
  logic [DATA_WIDTH-1:0] o_data;

  svc_skidbuf #(
      .DATA_WIDTH(DATA_WIDTH),
      .OPT_OUTREG(1)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(o_valid),
      .o_ready(i_ready),
      .i_data (o_data),
      .o_valid(i_valid),
      .i_ready(o_ready),
      .o_data (i_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      o_valid <= 0;
      o_data  <= 0;
      o_ready <= 0;
    end
  end

  always @(posedge clk) begin
    if (o_valid && i_ready) begin
      o_valid <= 0;
    end
  end

  // Test basic data flow
  task test_basic_flow;
    begin
      o_ready = 1;
      o_valid = 1;
      o_data  = 8'hA5;
      `TICK(clk);

      `CHECK_EQ(i_data, 8'hA5);
      `CHECK_TRUE(i_valid);

      `TICK(clk);
      `CHECK_FALSE(i_valid);
    end
  endtask

  // Test back pressure handling
  task test_backpressure;
    begin
      o_ready = 0;
      o_valid = 1;
      o_data  = 8'h55;
      `TICK(clk);
      `CHECK_EQ(i_data, 8'h55);
      `CHECK_TRUE(i_valid);
      `CHECK_TRUE(i_ready);

      o_valid = 1;
      o_data  = 8'hAA;
      `TICK(clk);
      `CHECK_EQ(i_data, 8'h55);

      o_ready = 1;
      `TICK(clk);
      `CHECK_EQ(i_data, 8'hAA);
      `CHECK_TRUE(i_valid);
    end
  endtask

  // Test continuous data flow
  task test_continious_flow;
    begin
      o_ready = 1;

      for (int i = 0; i < 4; i++) begin
        o_valid = 1;
        o_data  = DATA_WIDTH'(i);
        `TICK(clk);
        `CHECK_EQ(i_data, DATA_WIDTH'(i));
      end
    end
  endtask

  // Test reset behavior
  task test_reset;
    begin
      o_ready = 0;
      o_valid = 1;
      o_data  = 8'h42;
      `TICK(clk);

      rst_n = 0;
      `TICK(clk);
      `CHECK_FALSE(i_valid);
      `CHECK_TRUE(i_ready);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_skidbuf_reg_tb);

  `TEST_CASE(test_basic_flow);
  `TEST_CASE(test_backpressure);
  `TEST_CASE(test_continious_flow);
  `TEST_CASE(test_reset);

  `TEST_SUITE_END();

endmodule
