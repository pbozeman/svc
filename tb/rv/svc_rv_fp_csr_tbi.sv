`include "svc_unit.sv"
`include "svc_rv_fp_csr.sv"

module svc_rv_fp_csr_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Include constants for CSR addresses and operations
  `include "svc_rv_defs.svh"

  logic [11:0] csr_addr;
  logic [ 2:0] csr_op;
  logic [31:0] csr_wdata;
  logic        csr_en;
  logic [31:0] csr_rdata;
  logic        csr_hit;
  logic [ 2:0] frm;
  logic        fflags_set_en;
  logic [ 4:0] fflags_set;

  //
  // DUT instantiation
  //
  svc_rv_fp_csr uut (
      .clk          (clk),
      .rst_n        (rst_n),
      .csr_addr     (csr_addr),
      .csr_op       (csr_op),
      .csr_wdata    (csr_wdata),
      .csr_en       (csr_en),
      .csr_rdata    (csr_rdata),
      .csr_hit      (csr_hit),
      .frm          (frm),
      .fflags_set_en(fflags_set_en),
      .fflags_set   (fflags_set)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      csr_addr      <= '0;
      csr_op        <= '0;
      csr_wdata     <= '0;
      csr_en        <= '0;
      fflags_set_en <= '0;
      fflags_set    <= '0;
    end
  end

  //
  // Test: Reset values
  //
  task automatic test_reset();
    `TICK(clk);
    csr_addr = CSR_FFLAGS;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);

    csr_addr = CSR_FRM;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);

    csr_addr = CSR_FCSR;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0);

    `CHECK_EQ(frm, 3'h0);
  endtask

  //
  // Test: Address hit detection
  //
  task automatic test_address_hit();
    csr_addr = CSR_FFLAGS;
    `TICK(clk);
    `CHECK_EQ(csr_hit, 1'b1);

    csr_addr = CSR_FRM;
    `TICK(clk);
    `CHECK_EQ(csr_hit, 1'b1);

    csr_addr = CSR_FCSR;
    `TICK(clk);
    `CHECK_EQ(csr_hit, 1'b1);

    // Non-FP CSR should not hit
    csr_addr = CSR_CYCLE;
    `TICK(clk);
    `CHECK_EQ(csr_hit, 1'b0);

    csr_addr = 12'hFFF;
    `TICK(clk);
    `CHECK_EQ(csr_hit, 1'b0);
  endtask

  //
  // Test: CSRRW to fflags
  //
  task automatic test_csrrw_fflags();
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h1F;  // All flags set
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h1F);

    // Write different value
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h0A;  // DZ, UF
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h0A);
  endtask

  //
  // Test: CSRRS to fflags (set bits)
  //
  task automatic test_csrrs_fflags();
    // First clear
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h00;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    // Set some bits
    csr_op    = FUNCT3_CSRRS;
    csr_wdata = 32'h05;  // NX, OF
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h05);

    // Set more bits (should OR)
    csr_op    = FUNCT3_CSRRS;
    csr_wdata = 32'h0A;  // UF, DZ
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h0F);
  endtask

  //
  // Test: CSRRC to fflags (clear bits)
  //
  task automatic test_csrrc_fflags();
    // First set all
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h1F;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    // Clear some bits
    csr_op    = FUNCT3_CSRRC;
    csr_wdata = 32'h05;  // Clear NX, OF
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h1A);
  endtask

  //
  // Test: frm write and output
  //
  task automatic test_frm_write();
    csr_addr  = CSR_FRM;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h03;  // RUP
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h03);
    `CHECK_EQ(frm, 3'h3);

    // Change to RTZ
    csr_wdata = 32'h01;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h01);
    `CHECK_EQ(frm, 3'h1);
  endtask

  //
  // Test: fcsr combined access
  //
  task automatic test_fcsr_combined();
    // Write via fcsr
    csr_addr  = CSR_FCSR;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'hAB;  // frm=5, fflags=0x0B
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'hAB);
    `CHECK_EQ(frm, 3'h5);

    // Read back via individual CSRs
    csr_addr = CSR_FFLAGS;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h0B);

    csr_addr = CSR_FRM;
    `TICK(clk);
    `CHECK_EQ(csr_rdata, 32'h05);
  endtask

  //
  // Test: Flag accumulation from FPU
  //
  task automatic test_flag_accumulation();
    // Clear flags
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h00;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    // FPU sets NX
    fflags_set    = 5'b00001;  // NX
    fflags_set_en = 1'b1;
    `TICK(clk);
    fflags_set_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h01);

    // FPU sets OF (should accumulate)
    fflags_set    = 5'b00100;  // OF
    fflags_set_en = 1'b1;
    `TICK(clk);
    fflags_set_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h05);  // NX | OF

    // FPU sets NV (should accumulate)
    fflags_set    = 5'b10000;  // NV
    fflags_set_en = 1'b1;
    `TICK(clk);
    fflags_set_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h15);  // NX | OF | NV
  endtask

  //
  // Test: CSR immediate variants
  //
  task automatic test_csr_immediate();
    // Clear flags
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h00;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    // CSRRSI with zimm
    csr_op    = FUNCT3_CSRRSI;
    csr_wdata = 32'h03;  // zimm
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h03);

    // CSRRCI with zimm
    csr_op    = FUNCT3_CSRRCI;
    csr_wdata = 32'h01;  // Clear bit 0
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h02);

    // CSRRWI with zimm
    csr_op    = FUNCT3_CSRRWI;
    csr_wdata = 32'h1F;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h1F);
  endtask

  //
  // Test: CSR disabled (csr_en=0)
  //
  task automatic test_csr_disabled();
    // Set initial value
    csr_addr  = CSR_FFLAGS;
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h0A;
    csr_en    = 1'b1;
    `TICK(clk);
    csr_en = 1'b0;
    `TICK(clk);

    `CHECK_EQ(csr_rdata, 32'h0A);

    // Try to write with csr_en=0
    csr_op    = FUNCT3_CSRRW;
    csr_wdata = 32'h1F;
    csr_en    = 1'b0;
    `TICK(clk);
    `TICK(clk);

    // Value should not change
    `CHECK_EQ(csr_rdata, 32'h0A);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_fp_csr_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_address_hit);
  `TEST_CASE(test_csrrw_fflags);
  `TEST_CASE(test_csrrs_fflags);
  `TEST_CASE(test_csrrc_fflags);
  `TEST_CASE(test_frm_write);
  `TEST_CASE(test_fcsr_combined);
  `TEST_CASE(test_flag_accumulation);
  `TEST_CASE(test_csr_immediate);
  `TEST_CASE(test_csr_disabled);
  `TEST_SUITE_END();

endmodule
