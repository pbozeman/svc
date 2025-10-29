`include "svc_unit.sv"
`include "svc_axil_regfile.sv"

module svc_axil_regfile_tb;
  parameter N = 5;
  parameter DW = 32;
  parameter A_AW = 16;
  parameter A_DW = 32;
  parameter A_SW = A_DW / 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Register storage
  logic [   N-1:0][DW-1:0] r_reg;
  logic [   N-1:0][DW-1:0] r_reg_next;

  logic [A_AW-1:0]         m_axil_awaddr;
  logic                    m_axil_awvalid;
  logic                    m_axil_awready;
  logic [A_DW-1:0]         m_axil_wdata;
  logic [A_SW-1:0]         m_axil_wstrb;
  logic                    m_axil_wvalid;
  logic                    m_axil_wready;
  logic                    m_axil_bvalid;
  logic [     1:0]         m_axil_bresp;
  logic                    m_axil_bready;

  logic                    m_axil_arvalid;
  logic [A_AW-1:0]         m_axil_araddr;
  logic                    m_axil_arready;
  logic                    m_axil_rvalid;
  logic [A_DW-1:0]         m_axil_rdata;
  logic [     1:0]         m_axil_rresp;
  logic                    m_axil_rready;

  parameter [N-1:0] REG_WRITE_MASK = 5'b00101;

  // parameter ADDR_0 = 16'h0000;
  parameter ADDR_1 = 16'h0004;
  parameter ADDR_2 = 16'h0008;
  // parameter ADDR_3 = 16'h000C;
  // parameter ADDR_4 = 16'h000E;

  parameter INIT_0 = 32'h00000000;
  parameter INIT_1 = 32'hABCDEF01;
  parameter INIT_2 = 32'h12345678;
  parameter INIT_3 = 32'hDEADBEEF;
  parameter INIT_4 = 32'h86754321;

  // Register update logic
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      r_reg[0] <= INIT_0;
      r_reg[1] <= INIT_1;
      r_reg[2] <= INIT_2;
      r_reg[3] <= INIT_3;
      r_reg[4] <= INIT_4;
    end else begin
      r_reg <= r_reg_next;
    end
  end

  svc_axil_regfile #(
      .N              (N),
      .DATA_WIDTH     (DW),
      .AXIL_ADDR_WIDTH(A_AW),
      .AXIL_DATA_WIDTH(A_DW),
      .AXIL_STRB_WIDTH(A_SW),
      .REG_WRITE_MASK (REG_WRITE_MASK)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .r_val     (r_reg),
      .r_val_next(r_reg_next),

      .s_axil_awaddr (m_axil_awaddr),
      .s_axil_awvalid(m_axil_awvalid),
      .s_axil_awready(m_axil_awready),
      .s_axil_wdata  (m_axil_wdata),
      .s_axil_wstrb  (m_axil_wstrb),
      .s_axil_wvalid (m_axil_wvalid),
      .s_axil_wready (m_axil_wready),
      .s_axil_bvalid (m_axil_bvalid),
      .s_axil_bresp  (m_axil_bresp),
      .s_axil_bready (m_axil_bready),

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_arready(m_axil_arready),
      .s_axil_rvalid (m_axil_rvalid),
      .s_axil_rdata  (m_axil_rdata),
      .s_axil_rresp  (m_axil_rresp),
      .s_axil_rready (m_axil_rready)
  );

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axil_awaddr  <= '0;
      m_axil_awvalid <= 1'b0;
      m_axil_wdata   <= '0;
      m_axil_wstrb   <= '0;
      m_axil_wvalid  <= 1'b0;
      m_axil_bready  <= 1'b1;

      m_axil_araddr  <= '0;
      m_axil_arvalid <= 1'b0;
      m_axil_rready  <= 1'b1;
    end else begin
      m_axil_awvalid <= m_axil_awvalid && !m_axil_awready;
      m_axil_wvalid  <= m_axil_awvalid && !m_axil_wready;
      m_axil_arvalid <= m_axil_arvalid && !m_axil_arready;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(r_reg[0], INIT_0);
    `CHECK_EQ(r_reg[1], INIT_1);
    `CHECK_EQ(r_reg[2], INIT_2);
    `CHECK_EQ(r_reg[3], INIT_3);

    `CHECK_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_read();
    m_axil_araddr  = ADDR_1;
    m_axil_arvalid = 1'b1;
    m_axil_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
    `CHECK_EQ(m_axil_rdata, INIT_1);
    `CHECK_EQ(m_axil_rresp, 2'b00);
  endtask

  task automatic test_read_bad_addr();
    m_axil_araddr  = N * 4;
    m_axil_arvalid = 1'b1;
    m_axil_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
    `CHECK_EQ(m_axil_rresp, 2'b11);
  endtask

  task automatic test_write();
    m_axil_awaddr  = ADDR_2;
    m_axil_awvalid = 1'b1;
    m_axil_wvalid  = 1'b1;
    m_axil_wstrb   = '1;
    m_axil_wdata   = 32'h08675309;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b00);
    `CHECK_EQ(r_reg[2], 32'h08675309);
  endtask

  task automatic test_write_bad_addr();
    m_axil_awaddr  = N * 4;
    m_axil_awvalid = 1'b1;
    m_axil_wvalid  = 1'b1;
    m_axil_wstrb   = '1;
    m_axil_wdata   = 32'h08675309;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b11);
  endtask

  task automatic test_write_ro();
    m_axil_awaddr  = ADDR_1;
    m_axil_awvalid = 1'b1;
    m_axil_wvalid  = 1'b1;
    m_axil_wstrb   = '1;
    m_axil_wdata   = 32'h08675309;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b10);
    `CHECK_EQ(r_reg[1], INIT_1);
  endtask

  task automatic test_write_partial();
    m_axil_awaddr  = ADDR_2;
    m_axil_awvalid = 1'b1;
    m_axil_wvalid  = 1'b1;
    m_axil_wstrb   = 1;
    m_axil_wdata   = 32'h08675309;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b10);
    `CHECK_EQ(r_reg[2], INIT_2);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_regfile_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_read);
  `TEST_CASE(test_read_bad_addr);
  `TEST_CASE(test_write);
  `TEST_CASE(test_write_bad_addr);
  `TEST_CASE(test_write_ro);
  `TEST_CASE(test_write_partial);
  `TEST_SUITE_END();

endmodule
