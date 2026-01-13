`include "svc_unit.sv"

`include "svc_mux_onehot.sv"

module svc_mux_onehot_tbi;
  localparam WIDTH = 32;
  localparam N = 4;

  logic [      N-1:0] sel;
  logic [N*WIDTH-1:0] data;
  logic [  WIDTH-1:0] out;

  svc_mux_onehot #(
      .WIDTH(WIDTH),
      .N    (N)
  ) uut (
      .sel (sel),
      .data(data),
      .out (out)
  );

  task automatic test_reset;
    sel  = '0;
    data = '0;
    #1;
    `CHECK_EQ(out, '0);
  endtask

  task automatic test_select_each;
    data = {32'hDDDD_DDDD, 32'hCCCC_CCCC, 32'hBBBB_BBBB, 32'hAAAA_AAAA};

    sel  = 4'b0001;
    #1;
    `CHECK_EQ(out, 32'hAAAA_AAAA);

    sel = 4'b0010;
    #1;
    `CHECK_EQ(out, 32'hBBBB_BBBB);

    sel = 4'b0100;
    #1;
    `CHECK_EQ(out, 32'hCCCC_CCCC);

    sel = 4'b1000;
    #1;
    `CHECK_EQ(out, 32'hDDDD_DDDD);
  endtask

  task automatic test_no_select;
    data = {32'hDDDD_DDDD, 32'hCCCC_CCCC, 32'hBBBB_BBBB, 32'hAAAA_AAAA};

    sel  = 4'b0000;
    #1;
    `CHECK_EQ(out, '0);
  endtask

  `TEST_SUITE_BEGIN(svc_mux_onehot_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_select_each);
  `TEST_CASE(test_no_select);
  `TEST_SUITE_END();

endmodule
