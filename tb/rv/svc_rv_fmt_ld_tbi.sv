`include "svc_unit.sv"
`include "svc_rv_fmt_ld.sv"

module svc_rv_fmt_ld_tbi;
  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  logic [XLEN-1:0] data_in;
  logic [     1:0] addr;
  logic [     2:0] funct3;
  logic [XLEN-1:0] data_out;

  svc_rv_fmt_ld #(
      .XLEN(XLEN)
  ) uut (
      .data_in (data_in),
      .addr    (addr),
      .funct3  (funct3),
      .data_out(data_out)
  );

  //
  // Test: Load byte signed
  //
  task automatic test_load_byte_signed;
    data_in = 32'h12345678;
    funct3  = FUNCT3_LB;

    //
    // Test all byte positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h00000078);

    addr = 2'b01;
    `CHECK_EQ(data_out, 32'h00000056);

    addr = 2'b10;
    `CHECK_EQ(data_out, 32'h00000034);

    addr = 2'b11;
    `CHECK_EQ(data_out, 32'h00000012);

    //
    // Test sign extension with negative byte
    //
    data_in = 32'h000000FF;
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'hFFFFFFFF);

    data_in = 32'h000080FF;
    addr    = 2'b01;
    `CHECK_EQ(data_out, 32'hFFFFFF80);
  endtask

  //
  // Test: Load byte unsigned
  //
  task automatic test_load_byte_unsigned;
    data_in = 32'h12345678;
    funct3  = FUNCT3_LBU;

    //
    // Test all byte positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h00000078);

    addr = 2'b01;
    `CHECK_EQ(data_out, 32'h00000056);

    //
    // Test zero extension (no sign extension)
    //
    data_in = 32'h000000FF;
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h000000FF);

    data_in = 32'h000080FF;
    addr    = 2'b01;
    `CHECK_EQ(data_out, 32'h00000080);
  endtask

  //
  // Test: Load halfword signed
  //
  task automatic test_load_halfword_signed;
    data_in = 32'h12345678;
    funct3  = FUNCT3_LH;

    //
    // Test both halfword positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h00005678);

    addr = 2'b10;
    `CHECK_EQ(data_out, 32'h00001234);

    //
    // Test sign extension with negative halfword
    //
    data_in = 32'h0000FFFF;
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'hFFFFFFFF);

    data_in = 32'h8000FFFF;
    addr    = 2'b10;
    `CHECK_EQ(data_out, 32'hFFFF8000);
  endtask

  //
  // Test: Load halfword unsigned
  //
  task automatic test_load_halfword_unsigned;
    data_in = 32'h12345678;
    funct3  = FUNCT3_LHU;

    //
    // Test both halfword positions
    //
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h00005678);

    addr = 2'b10;
    `CHECK_EQ(data_out, 32'h00001234);

    //
    // Test zero extension (no sign extension)
    //
    data_in = 32'h0000FFFF;
    addr    = 2'b00;
    `CHECK_EQ(data_out, 32'h0000FFFF);

    data_in = 32'h8000FFFF;
    addr    = 2'b10;
    `CHECK_EQ(data_out, 32'h00008000);
  endtask

  //
  // Test: Load word
  //
  task automatic test_load_word;
    data_in = 32'h12345678;
    funct3  = FUNCT3_LW;
    addr    = 2'b00;

    `CHECK_EQ(data_out, 32'h12345678);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_fmt_ld_tbi);
  `TEST_CASE(test_load_byte_signed);
  `TEST_CASE(test_load_byte_unsigned);
  `TEST_CASE(test_load_halfword_signed);
  `TEST_CASE(test_load_halfword_unsigned);
  `TEST_CASE(test_load_word);
  `TEST_SUITE_END();

endmodule
