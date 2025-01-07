`include "svc_unit.sv"

`include "svc_sync_fifo.sv"

module svc_sync_fifo_tb;
  parameter ADDR_WIDTH = 4;
  parameter DATA_WIDTH = 8;
  parameter MEM_DEPTH = 1 << ADDR_WIDTH;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                  w_inc;
  logic [DATA_WIDTH-1:0] w_data;
  logic                  w_full;

  logic                  r_inc;
  logic                  r_empty;
  logic [DATA_WIDTH-1:0] r_data;

  svc_sync_fifo #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) uut (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (w_inc),
      .w_data     (w_data),
      .w_half_full(),
      .w_full     (w_full),
      .r_inc      (r_inc),
      .r_empty    (r_empty),
      .r_data     (r_data)
  );

  task automatic setup;
    begin
      w_inc  = 0;
      w_data = 0;
      r_inc  = 0;
    end
  endtask

  task automatic test_init;
    `CHECK_EQ(r_empty, 1'b1)
    `CHECK_EQ(w_full, 1'b0)
  endtask

  task automatic test_single_write_read;
    logic [DATA_WIDTH-1:0] data = DATA_WIDTH'(128);

    // write
    w_data = data;
    w_inc  = 1;
    `TICK(clk);

    `CHECK_FALSE(r_empty);
    `CHECK_EQ(r_data, data);
    w_inc = 0;

    // read
    r_inc = 1;
    `TICK(clk);

    `CHECK_TRUE(r_empty);
  endtask

  task automatic test_fill_fifo;
    for (int i = 0; i < MEM_DEPTH; i++) begin
      w_data = i[DATA_WIDTH-1:0];
      w_inc  = 1;
      `TICK(clk);

      `CHECK_EQ(w_full, (i == MEM_DEPTH - 1));
    end

    w_inc = 0;
    `CHECK_TRUE(w_full);
  endtask

  task automatic test_read_full_fifo;
    test_fill_fifo();

    for (int i = 0; i < MEM_DEPTH; i++) begin
      `CHECK_EQ(r_data, DATA_WIDTH'(i));
      r_inc = 1;
      `TICK(clk);

      `CHECK_EQ(r_empty, (i == MEM_DEPTH - 1));
    end

    r_inc = 0;
    `CHECK_TRUE(r_empty);
  endtask

  task automatic test_write_read_same_clock;
    logic [DATA_WIDTH-1:0] data1 = DATA_WIDTH'(64);
    logic [DATA_WIDTH-1:0] data2 = DATA_WIDTH'(128);

    // write
    w_data = data1;
    w_inc  = 1;
    `TICK(clk);

    `CHECK_FALSE(r_empty);
    `CHECK_EQ(r_data, data1);

    // second write with read
    w_data = data2;
    r_inc  = 1;
    `TICK(clk);

    `CHECK_EQ(r_empty, 1'b0)
    `CHECK_EQ(r_data, data2);
    w_inc = 0;

    // read
    r_inc = 1;
    `TICK(clk);

    `CHECK_TRUE(r_empty);
  endtask

  `TEST_SUITE_BEGIN(svc_sync_fifo_tb);
  `TEST_SETUP(setup);

  `TEST_CASE(test_init);
  `TEST_CASE(test_single_write_read);
  `TEST_CASE(test_fill_fifo);
  `TEST_CASE(test_write_read_same_clock);

  `TEST_SUITE_END();

endmodule
