`include "svc_unit.sv"

`include "svc_cdc_fifo.sv"

// This is only a very basic test. The design was implemented directly from
// the paper with only cosmetic changes, so I'm comfortable with it.
// Plus, doing a deeper verification would better be done with formal
// verification anyway, but it's a bit tricky. See the note in
// cdc module.

module svc_cdc_fifo_tb;
  parameter ADDR_WIDTH = 4;
  parameter DATA_WIDTH = 8;
  // parameter MEM_DEPTH = 1 << ADDR_WIDTH;

  `TEST_CLK_NS(w_clk, 10);
  logic                  w_rst_n;
  logic                  w_inc;
  logic [DATA_WIDTH-1:0] w_data;
  logic                  w_full;

  `TEST_CLK_NS(r_clk, 14);
  logic                  r_rst_n;
  logic                  r_inc;
  logic [DATA_WIDTH-1:0] r_data;
  logic                  r_empty;

  svc_cdc_fifo #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) uut (
      .w_clk  (w_clk),
      .w_rst_n(w_rst_n),
      .w_inc  (w_inc),
      .w_data (w_data),
      .w_full (w_full),

      .r_clk  (r_clk),
      .r_rst_n(r_rst_n),
      .r_inc  (r_inc),
      .r_empty(r_empty),
      .r_data (r_data)
  );

  // we have to take over reset because the RST macros can't handle 2 clocks
  // and reset signals.
  task setup;
    w_rst_n = 1'b0;
    r_rst_n = 1'b0;

    // r_clk is longer
    repeat (5) @(posedge r_clk);

    w_rst_n = 1'b1;
    r_rst_n = 1'b1;
  endtask

  always_ff @(posedge w_clk) begin
    if (~w_rst_n) begin
      w_inc  <= 0;
      w_data <= 0;
    end
  end

  always_ff @(posedge r_clk) begin
    if (~r_rst_n) begin
      r_inc <= 0;
    end
  end

  task automatic test_init;
    `CHECK_TRUE(r_empty);
    `CHECK_FALSE(w_full);
  endtask

  task automatic test_basic;
    logic [DATA_WIDTH-1:0] data = DATA_WIDTH'(42);

    // Write data
    w_inc = 1;
    for (int i = 0; i < 16; i++) begin
      w_data = data + DATA_WIDTH'(i);
      `TICK(w_clk);
      if (i != 15) begin
        `CHECK_FALSE(w_full);
      end
    end

    // stop writes and switch to read
    w_inc = 0;
    `CHECK_TRUE(w_full);

    // Read data
    `CHECK_FALSE(r_empty);
    r_inc = 1;
    for (int i = 0; i < 16; i++) begin
      `CHECK_EQ(r_data, data + DATA_WIDTH'(i));
      `TICK(r_clk);
      if (i != 15) begin
        `CHECK_FALSE(r_empty);
      end
    end

    r_inc = 0;
    `CHECK_TRUE(r_empty);
  endtask

  `TEST_SUITE_BEGIN(svc_cdc_fifo_tb);

  `TEST_SETUP(setup);
  `TEST_CASE(test_init);
  `TEST_CASE(test_basic);

  `TEST_SUITE_END();

endmodule
