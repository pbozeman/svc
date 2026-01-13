`include "svc_unit.sv"
`include "svc_rv_fmt_st.sv"

module svc_rv_fmt_st_tbi;
  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  logic [  XLEN-1:0] data_in;
  logic [       1:0] addr;
  logic [       2:0] funct3;
  logic [  XLEN-1:0] data_out;
  logic [XLEN/8-1:0] wstrb;

  svc_rv_fmt_st #(
      .XLEN(XLEN)
  ) uut (
      .data_in (data_in),
      .addr    (addr),
      .funct3  (funct3),
      .data_out(data_out),
      .wstrb   (wstrb)
  );

  //
  // Test: Store byte
  //
  task automatic test_store_byte;
    data_in = 32'h12345678;
    funct3  = FUNCT3_SB;

    //
    // Test all byte positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h78787878);
    `CHECK_EQ(wstrb, 4'b0001);

    addr = 2'b01;
    `CHECK_EQ(data_out, 32'h78787878);
    `CHECK_EQ(wstrb, 4'b0010);

    addr = 2'b10;
    `CHECK_EQ(data_out, 32'h78787878);
    `CHECK_EQ(wstrb, 4'b0100);

    addr = 2'b11;
    `CHECK_EQ(data_out, 32'h78787878);
    `CHECK_EQ(wstrb, 4'b1000);
  endtask

  //
  // Test: Store halfword
  //
  task automatic test_store_halfword;
    data_in = 32'h12345678;
    funct3  = FUNCT3_SH;

    //
    // Test both halfword positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h56785678);
    `CHECK_EQ(wstrb, 4'b0011);

    addr = 2'b10;
    `CHECK_EQ(data_out, 32'h56785678);
    `CHECK_EQ(wstrb, 4'b1100);
  endtask

  //
  // Test: Store word
  //
  task automatic test_store_word;
    data_in = 32'h12345678;
    funct3  = FUNCT3_SW;
    addr    = 2'b00;

    `CHECK_EQ(data_out, 32'h12345678);
    `CHECK_EQ(wstrb, 4'b1111);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_fmt_st_tbi);
  `TEST_CASE(test_store_byte);
  `TEST_CASE(test_store_halfword);
  `TEST_CASE(test_store_word);
  `TEST_SUITE_END();

endmodule
