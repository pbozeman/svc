`include "svc_unit.sv"
`include "svc_rv_csr.sv"

module svc_rv_csr_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  `include "svc_rv_defs.svh"

  logic [11:0] csr_addr;
  logic [31:0] csr_rdata;
  logic        instret_inc;

  svc_rv_csr uut (
      .clk        (clk),
      .rst_n      (rst_n),
      .csr_addr   (csr_addr),
      .csr_rdata  (csr_rdata),
      .instret_inc(instret_inc)
  );

  //
  // Test: CYCLE counter increments every clock cycle
  //
  task automatic test_cycle_increment;
    logic [31:0] expected_cycle;
    logic [31:0] expected_cycleh;

    expected_cycle  = uut.cycle;
    expected_cycleh = uut.cycleh;

    `TICK(clk);
    expected_cycle = expected_cycle + 1;
    `CHECK_EQ(uut.cycle, expected_cycle);
    `CHECK_EQ(uut.cycleh, expected_cycleh);

    `TICK(clk);
    expected_cycle = expected_cycle + 1;
    `CHECK_EQ(uut.cycle, expected_cycle);
    `CHECK_EQ(uut.cycleh, expected_cycleh);

    `TICK(clk);
    expected_cycle = expected_cycle + 1;
    `CHECK_EQ(uut.cycle, expected_cycle);
    `CHECK_EQ(uut.cycleh, expected_cycleh);
  endtask

  //
  // Test: INSTRET counter increments on instret_inc
  //
  task automatic test_instret_increment;
    logic [31:0] expected_instret;
    logic [31:0] expected_instreth;

    instret_inc       = 1'b0;
    expected_instret  = uut.instret;
    expected_instreth = uut.instreth;

    `TICK(clk);
    `CHECK_EQ(uut.instret, expected_instret);
    `CHECK_EQ(uut.instreth, expected_instreth);

    instret_inc = 1'b1;
    `TICK(clk);
    expected_instret = expected_instret + 1;
    `CHECK_EQ(uut.instret, expected_instret);
    `CHECK_EQ(uut.instreth, expected_instreth);

    instret_inc = 1'b0;
    `TICK(clk);
    `CHECK_EQ(uut.instret, expected_instret);
    `CHECK_EQ(uut.instreth, expected_instreth);

    instret_inc = 1'b1;
    `TICK(clk);
    expected_instret = expected_instret + 1;
    `CHECK_EQ(uut.instret, expected_instret);
    `CHECK_EQ(uut.instreth, expected_instreth);
  endtask

  //
  // Test: 64-bit CYCLE overflow from low to high word
  //
  task automatic test_cycle_overflow;
    uut.cycle  = 32'hFFFFFFFE;
    uut.cycleh = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(uut.cycle, 32'hFFFFFFFF);
    `CHECK_EQ(uut.cycleh, 32'h00000000);

    `TICK(clk);
    `CHECK_EQ(uut.cycle, 32'h00000000);
    `CHECK_EQ(uut.cycleh, 32'h00000001);

    `TICK(clk);
    `CHECK_EQ(uut.cycle, 32'h00000001);
    `CHECK_EQ(uut.cycleh, 32'h00000001);
  endtask

  //
  // Test: 64-bit INSTRET overflow from low to high word
  //
  task automatic test_instret_overflow;
    uut.instret  = 32'hFFFFFFFE;
    uut.instreth = 32'h00000000;
    instret_inc  = 1'b1;

    `TICK(clk);
    `CHECK_EQ(uut.instret, 32'hFFFFFFFF);
    `CHECK_EQ(uut.instreth, 32'h00000000);

    `TICK(clk);
    `CHECK_EQ(uut.instret, 32'h00000000);
    `CHECK_EQ(uut.instreth, 32'h00000001);

    `TICK(clk);
    `CHECK_EQ(uut.instret, 32'h00000001);
    `CHECK_EQ(uut.instreth, 32'h00000001);

    instret_inc = 1'b0;
  endtask

  //
  // Test: CSR read of CYCLE
  //
  task automatic test_read_cycle;
    csr_addr = CSR_CYCLE;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.cycle);

    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.cycle);
  endtask

  //
  // Test: CSR read of CYCLEH
  //
  task automatic test_read_cycleh;
    csr_addr = CSR_CYCLEH;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.cycleh);

    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.cycleh);
  endtask

  //
  // Test: CSR read of INSTRET
  //
  task automatic test_read_instret;
    csr_addr    = CSR_INSTRET;
    instret_inc = 1'b1;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.instret);

    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.instret);

    instret_inc = 1'b0;
  endtask

  //
  // Test: CSR read of INSTRETH
  //
  task automatic test_read_instreth;
    csr_addr = CSR_INSTRETH;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.instreth);

    `TICK(clk);
    `CHECK_EQ(csr_rdata, uut.instreth);
  endtask

  //
  // Test: Invalid CSR address returns zero
  //
  task automatic test_invalid_csr;
    csr_addr = 12'h000;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);

    csr_addr = 12'hFFF;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);

    csr_addr = 12'h123;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_csr_tb);
  `TEST_CASE(test_cycle_increment);
  `TEST_CASE(test_instret_increment);
  `TEST_CASE(test_cycle_overflow);
  `TEST_CASE(test_instret_overflow);
  `TEST_CASE(test_read_cycle);
  `TEST_CASE(test_read_cycleh);
  `TEST_CASE(test_read_instret);
  `TEST_CASE(test_read_instreth);
  `TEST_CASE(test_invalid_csr);
  `TEST_SUITE_END();

endmodule
