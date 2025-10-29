`include "svc_unit.sv"

`include "svc_sync_fifo_zl.sv"

module svc_sync_fifo_zl_tb;
  parameter AW = 4;
  parameter DW = 8;
  parameter MEM_DEPTH = 1 << AW;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic          w_inc;
  logic [DW-1:0] w_data;
  logic          w_full_n;

  logic          r_inc;
  logic [DW-1:0] r_data;
  logic          r_empty_n;

  svc_sync_fifo_zl #(
      .ADDR_WIDTH(AW),
      .DATA_WIDTH(DW)
  ) uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .w_inc    (w_inc),
      .w_data   (w_data),
      .w_full_n (w_full_n),
      .r_inc    (r_inc),
      .r_empty_n(r_empty_n),
      .r_data   (r_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      w_inc  <= 0;
      w_data <= 0;
      r_inc  <= 0;
    end
  end

  task automatic test_init;
    `CHECK_EQ(r_empty_n, 1'b0)
    `CHECK_EQ(w_full_n, 1'b1)
  endtask

  task automatic test_empty_zl;
    logic [DW-1:0] data = DW'(128);

    // write
    w_data = data;
    w_inc  = 1;

    `CHECK_EQ(r_empty_n, 1'b1);
    `CHECK_EQ(r_data, data);

    r_inc = 1;
    `TICK(clk);
    w_inc = 0;

    `CHECK_EQ(r_empty_n, 1'b0);
  endtask

  task automatic test_empty_defered_read;
    logic [DW-1:0] data = DW'(128);

    // write
    w_data = data;
    w_inc  = 1;

    `CHECK_EQ(r_empty_n, 1'b1);
    `CHECK_EQ(r_data, data);

    `TICK(clk);
    w_inc = 0;
    `CHECK_EQ(r_empty_n, 1'b1);
    `CHECK_EQ(r_data, data);
    r_inc = 1;

    `TICK(clk);
    `CHECK_EQ(r_empty_n, 1'b0);
  endtask

  task automatic test_fill_fifo;
    for (int i = 0; i < MEM_DEPTH; i++) begin
      w_data = i[DW-1:0];
      w_inc  = 1;
      `TICK(clk);

      `CHECK_NEQ(w_full_n, (i == MEM_DEPTH - 1));
    end

    w_inc = 0;
    `CHECK_EQ(w_full_n, 1'b0);
  endtask

  task automatic test_read_full_fifo;
    test_fill_fifo();

    for (int i = 0; i < MEM_DEPTH; i++) begin
      `CHECK_EQ(r_data, DW'(i));
      r_inc = 1;
      `TICK(clk);

      `CHECK_NEQ(r_empty_n, (i == MEM_DEPTH - 1));
    end

    r_inc = 0;
    `CHECK_EQ(r_empty_n, 1'b0);
  endtask

  task automatic test_write_read_same_clock;
    logic [DW-1:0] data1 = DW'(64);
    logic [DW-1:0] data2 = DW'(128);

    // write
    w_data = data1;
    w_inc  = 1;
    `TICK(clk);

    `CHECK_EQ(r_empty_n, 1'b1);
    `CHECK_EQ(r_data, data1);

    // second write with read
    w_data = data2;
    r_inc  = 1;
    `TICK(clk);

    `CHECK_EQ(r_empty_n, 1'b1)
    `CHECK_EQ(r_data, data2);
    w_inc = 0;

    // read
    r_inc = 1;
    `TICK(clk);

    `CHECK_EQ(r_empty_n, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_sync_fifo_zl_tb);

  `TEST_CASE(test_init);
  `TEST_CASE(test_empty_zl);
  `TEST_CASE(test_empty_defered_read);
  `TEST_CASE(test_fill_fifo);
  `TEST_CASE(test_write_read_same_clock);

  `TEST_SUITE_END();

endmodule
