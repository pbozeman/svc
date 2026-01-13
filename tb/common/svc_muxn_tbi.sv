`include "svc_unit.sv"
`include "svc_muxn.sv"

module svc_muxn_tbi;
  `TEST_CLK_NS(clk, 10);

  //
  // 4-way mux instance
  //
  localparam int WIDTH_4 = 8;
  localparam int N_4 = 4;

  logic [1:0] sel_4;
  logic [WIDTH_4-1:0] in_4_0, in_4_1, in_4_2, in_4_3;
  logic [WIDTH_4-1:0] out_4;

  svc_muxn #(
      .WIDTH(WIDTH_4),
      .N    (N_4)
  ) mux_4 (
      .sel (sel_4),
      .data({in_4_3, in_4_2, in_4_1, in_4_0}),
      .out (out_4)
  );

  //
  // 8-way mux instance
  //
  localparam int WIDTH_8 = 16;
  localparam int N_8 = 8;

  logic [2:0] sel_8;
  logic [WIDTH_8-1:0]
      in_8_0, in_8_1, in_8_2, in_8_3, in_8_4, in_8_5, in_8_6, in_8_7;
  logic [WIDTH_8-1:0] out_8;

  svc_muxn #(
      .WIDTH(WIDTH_8),
      .N    (N_8)
  ) mux_8 (
      .sel (sel_8),
      .data({in_8_7, in_8_6, in_8_5, in_8_4, in_8_3, in_8_2, in_8_1, in_8_0}),
      .out (out_8)
  );

  //
  // 3-way mux instance (non-power-of-2)
  //
  localparam int WIDTH_3 = 32;
  localparam int N_3 = 3;

  logic [1:0] sel_3;
  logic [WIDTH_3-1:0] in_3_0, in_3_1, in_3_2;
  logic [WIDTH_3-1:0] out_3;

  svc_muxn #(
      .WIDTH(WIDTH_3),
      .N    (N_3)
  ) mux_3 (
      .sel (sel_3),
      .data({in_3_2, in_3_1, in_3_0}),
      .out (out_3)
  );

  //
  // Test: 4-way mux basic selection
  //
  task automatic test_mux4_basic;
    in_4_0 = 8'hAA;
    in_4_1 = 8'hBB;
    in_4_2 = 8'hCC;
    in_4_3 = 8'hDD;

    sel_4  = 2'd0;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hAA);

    sel_4 = 2'd1;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hBB);

    sel_4 = 2'd2;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hCC);

    sel_4 = 2'd3;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hDD);
  endtask

  //
  // Test: 4-way mux with zero values
  //
  task automatic test_mux4_zeros;
    in_4_0 = 8'h00;
    in_4_1 = 8'h00;
    in_4_2 = 8'h00;
    in_4_3 = 8'h00;

    sel_4  = 2'd0;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'h00);

    sel_4 = 2'd2;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'h00);
  endtask

  //
  // Test: 4-way mux with all ones
  //
  task automatic test_mux4_ones;
    in_4_0 = 8'hFF;
    in_4_1 = 8'hFF;
    in_4_2 = 8'hFF;
    in_4_3 = 8'hFF;

    sel_4  = 2'd1;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hFF);

    sel_4 = 2'd3;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hFF);
  endtask

  //
  // Test: 8-way mux basic selection
  //
  task automatic test_mux8_basic;
    in_8_0 = 16'h0000;
    in_8_1 = 16'h1111;
    in_8_2 = 16'h2222;
    in_8_3 = 16'h3333;
    in_8_4 = 16'h4444;
    in_8_5 = 16'h5555;
    in_8_6 = 16'h6666;
    in_8_7 = 16'h7777;

    sel_8  = 3'd0;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h0000);

    sel_8 = 3'd3;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h3333);

    sel_8 = 3'd7;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h7777);
  endtask

  //
  // Test: 8-way mux all selections
  //
  task automatic test_mux8_all;
    in_8_0 = 16'h0000;
    in_8_1 = 16'h1234;
    in_8_2 = 16'h2468;
    in_8_3 = 16'h36A4;
    in_8_4 = 16'h48D0;
    in_8_5 = 16'h5B04;
    in_8_6 = 16'h6D38;
    in_8_7 = 16'h7F6C;

    sel_8  = 3'd0;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h0000);

    sel_8 = 3'd1;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h1234);

    sel_8 = 3'd2;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h2468);

    sel_8 = 3'd3;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h36A4);

    sel_8 = 3'd4;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h48D0);

    sel_8 = 3'd5;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h5B04);

    sel_8 = 3'd6;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h6D38);

    sel_8 = 3'd7;
    `TICK(clk);
    `CHECK_EQ(out_8, 16'h7F6C);
  endtask

  //
  // Test: 3-way mux (non-power-of-2)
  //
  task automatic test_mux3_basic;
    in_3_0 = 32'hAAAAAAAA;
    in_3_1 = 32'hBBBBBBBB;
    in_3_2 = 32'hCCCCCCCC;

    sel_3  = 2'd0;
    `TICK(clk);
    `CHECK_EQ(out_3, 32'hAAAAAAAA);

    sel_3 = 2'd1;
    `TICK(clk);
    `CHECK_EQ(out_3, 32'hBBBBBBBB);

    sel_3 = 2'd2;
    `TICK(clk);
    `CHECK_EQ(out_3, 32'hCCCCCCCC);
  endtask

  //
  // Test: 3-way mux out-of-range selector
  //
  task automatic test_mux3_out_of_range;
    in_3_0 = 32'hAAAAAAAA;
    in_3_1 = 32'hBBBBBBBB;
    in_3_2 = 32'hCCCCCCCC;

    sel_3  = 2'd3;
    `TICK(clk);
    `CHECK_EQ(out_3, 32'hxxxxxxxx);
  endtask

  //
  // Test: Dynamic data changes
  //
  task automatic test_mux4_dynamic;
    sel_4  = 2'd1;
    in_4_1 = 8'h11;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'h11);

    in_4_1 = 8'h22;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'h22);

    in_4_1 = 8'hFF;
    `TICK(clk);
    `CHECK_EQ(out_4, 8'hFF);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_muxn_tbi);
  `TEST_CASE(test_mux4_basic);
  `TEST_CASE(test_mux4_zeros);
  `TEST_CASE(test_mux4_ones);
  `TEST_CASE(test_mux8_basic);
  `TEST_CASE(test_mux8_all);
  `TEST_CASE(test_mux3_basic);
  `TEST_CASE(test_mux3_out_of_range);
  `TEST_CASE(test_mux4_dynamic);
  `TEST_SUITE_END();

endmodule
