`include "svc_unit.sv"
`include "svc_rv_st_fmt.sv"

module svc_rv_st_fmt_tb;
  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  logic [  XLEN-1:0] data_in;
  logic [       1:0] addr;
  logic [       2:0] funct3;
  logic              mem_write;
  logic [  XLEN-1:0] data_out;
  logic [XLEN/8-1:0] wstrb;

  svc_rv_st_fmt #(
      .XLEN(XLEN)
  ) uut (
      .data_in  (data_in),
      .addr     (addr),
      .funct3   (funct3),
      .mem_write(mem_write),
      .data_out (data_out),
      .wstrb    (wstrb)
  );

  //
  // Test: Store byte
  //
  task automatic test_store_byte;
    data_in   = 32'h12345678;
    funct3    = FUNCT3_SB;
    mem_write = 1'b1;

    //
    // Test all byte positions
    //
    addr      = 2'b00;
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
    data_in   = 32'h12345678;
    funct3    = FUNCT3_SH;
    mem_write = 1'b1;

    //
    // Test both halfword positions
    //
    addr      = 2'b00;
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
    data_in   = 32'h12345678;
    funct3    = FUNCT3_SW;
    mem_write = 1'b1;
    addr      = 2'b00;

    `CHECK_EQ(data_out, 32'h12345678);
    `CHECK_EQ(wstrb, 4'b1111);
  endtask

  //
  // Test: Write disabled
  //
  task automatic test_write_disabled;
    data_in   = 32'h12345678;
    funct3    = FUNCT3_SW;
    mem_write = 1'b0;
    addr      = 2'b00;

    `CHECK_EQ(wstrb, 4'b0000);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_st_fmt_tb);
  `TEST_CASE(test_store_byte);
  `TEST_CASE(test_store_halfword);
  `TEST_CASE(test_store_word);
  `TEST_CASE(test_write_disabled);
  `TEST_SUITE_END();

endmodule
