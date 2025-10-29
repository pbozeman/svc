`include "svc_unit.sv"

`include "svc_arbiter.sv"

// This is just a quick smoke test. The real testing is formal.

module svc_arbiter_tb;
  localparam NUM_M = 3;
  localparam IDX_WIDTH = $clog2(NUM_M);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [    NUM_M-1:0] request;
  logic                 done;

  logic                 grant_valid;
  logic [IDX_WIDTH-1:0] grant_idx;

  svc_arbiter #(
      .NUM_M(NUM_M)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .request    (request),
      .done       (done),
      .grant_valid(grant_valid),
      .grant_idx  (grant_idx)
  );

  task automatic test_initial;
    `CHECK_FALSE(grant_valid);
  endtask

  task automatic test_basic;
    request = 3'b110;
    done    = 1'b0;

    `TICK(clk);
    `CHECK_TRUE(grant_valid);
    `CHECK_EQ(grant_idx, 1);

    `TICK(clk);
    `CHECK_TRUE(grant_valid);
    `CHECK_EQ(grant_idx, 1);

    request = 3'b100;
    done    = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(grant_valid);
    `CHECK_EQ(grant_idx, 2);

    request = 0;
    done    = 1'b1;

    `TICK(clk);
    `CHECK_FALSE(grant_valid);
  endtask

  `TEST_SUITE_BEGIN(svc_arbiter_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
