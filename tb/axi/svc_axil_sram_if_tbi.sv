`include "svc_unit.sv"

`include "svc_axil_sram_if.sv"
`include "svc_model_sram_if.sv"

// The bulk of the testing happens with formal verification. This is just
// a quick smoke test.
module svc_axil_sram_if_tbi;
  parameter AW = 16;
  parameter DW = 16;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;
  parameter STRBW = (DW / 8);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [   AW-1:0] m_axil_awaddr;
  logic             m_axil_awvalid;
  logic             m_axil_awready;
  logic [   DW-1:0] m_axil_wdata;
  logic [STRBW-1:0] m_axil_wstrb;
  logic             m_axil_wvalid;
  logic             m_axil_wready;
  logic [      1:0] m_axil_bresp;
  logic             m_axil_bvalid;
  logic             m_axil_bready;

  logic             m_axil_arvalid;
  logic             m_axil_arready;
  logic [   AW-1:0] m_axil_araddr;
  logic [   DW-1:0] m_axil_rdata;
  logic [      1:0] m_axil_rresp;
  logic             m_axil_rvalid;
  logic             m_axil_rready;

  logic             sram_cmd_valid;
  logic             sram_cmd_ready;
  logic [  SAW-1:0] sram_cmd_addr;
  logic             sram_cmd_wr_en;
  logic [   DW-1:0] sram_cmd_wr_data;
  logic [STRBW-1:0] sram_cmd_wr_strb;
  logic             sram_resp_rd_valid;
  logic             sram_resp_rd_ready;
  logic [   DW-1:0] sram_resp_rd_data;

  // if true, test cases don't have to manage dropping valid signals
  logic             auto_valid;

  svc_axil_sram_if #(
      .AXIL_ADDR_WIDTH(AW),
      .AXIL_DATA_WIDTH(DW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awaddr (m_axil_awaddr),
      .s_axil_awvalid(m_axil_awvalid),
      .s_axil_awready(m_axil_awready),
      .s_axil_wdata  (m_axil_wdata),
      .s_axil_wstrb  (m_axil_wstrb),
      .s_axil_wvalid (m_axil_wvalid),
      .s_axil_wready (m_axil_wready),
      .s_axil_bresp  (m_axil_bresp),
      .s_axil_bvalid (m_axil_bvalid),
      .s_axil_bready (m_axil_bready),

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_arready(m_axil_arready),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_rdata  (m_axil_rdata),
      .s_axil_rresp  (m_axil_rresp),
      .s_axil_rvalid (m_axil_rvalid),
      .s_axil_rready (m_axil_rready),

      .sram_cmd_valid    (sram_cmd_valid),
      .sram_cmd_ready    (sram_cmd_ready),
      .sram_cmd_addr     (sram_cmd_addr),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_resp_rd_valid(sram_resp_rd_valid),
      .sram_resp_rd_ready(sram_resp_rd_ready),
      .sram_resp_rd_data (sram_resp_rd_data)
  );

  svc_model_sram_if #(
      .UNITIALIZED_READS_OK(1),
      .SRAM_ADDR_WIDTH     (SAW),
      .SRAM_DATA_WIDTH     (DW)
  ) svc_model_sram_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid   (sram_cmd_valid),
      .sram_cmd_ready   (sram_cmd_ready),
      .sram_cmd_addr    (sram_cmd_addr),
      .sram_cmd_wr_en   (sram_cmd_wr_en),
      .sram_cmd_wr_data (sram_cmd_wr_data),
      .sram_cmd_wr_strb (sram_cmd_wr_strb),
      .sram_resp_valid  (sram_resp_rd_valid),
      .sram_resp_ready  (sram_resp_rd_ready),
      .sram_resp_rd_data(sram_resp_rd_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_awaddr  <= '0;
      m_axil_awvalid <= 1'b0;
      m_axil_wdata   <= '0;
      m_axil_wstrb   <= '0;
      m_axil_wvalid  <= 1'b0;
      m_axil_bready  <= 1'b0;
      m_axil_arvalid <= 1'b0;
      m_axil_araddr  <= '0;
      m_axil_rready  <= 1'b0;

      auto_valid     <= 1'b1;
    end
  end

  // used in assertions with data returned by the fake sram above
  function automatic logic [DW-1:0] a_to_d(logic [AW-1:0] addr);
    // verilator lint_off: UNUSEDSIGNAL
    logic unused = |addr;
    // verilator lint_on: UNUSEDSIGNAL
    return DW'(addr[AW-1:LSB]);
  endfunction

  function automatic logic [SAW-1:0] a_to_sa(logic [AW-1:0] addr);
    // verilator lint_off: UNUSEDSIGNAL
    logic unused = |addr;
    // verilator lint_on: UNUSEDSIGNAL
    return SAW'(addr[AW-1:LSB]);
  endfunction

  // clear m valid flags on txn acceptance
  always_ff @(posedge clk) begin
    if (auto_valid) begin
      if (m_axil_awvalid && m_axil_awready) begin
        m_axil_awvalid <= 1'b0;
      end

      if (m_axil_wvalid && m_axil_wready) begin
        m_axil_wvalid <= 1'b0;
      end

      if (m_axil_arvalid && m_axil_arready) begin
        m_axil_arvalid <= 1'b0;
      end
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axil_bvalid);
    `CHECK_FALSE(m_axil_rvalid);
  endtask


  task automatic test_io;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hBABE);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr;
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = data;
    m_axil_wstrb   = '1;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_TRUE(sram_cmd_wr_en);

    `CHECK_WAIT_FOR(clk, m_axil_bvalid);
    `CHECK_EQ(m_axil_bresp, 2'b00);

    `TICK(clk);

    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr;
    m_axil_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_FALSE(sram_cmd_wr_en);

    `CHECK_WAIT_FOR(clk, m_axil_rvalid);
    `CHECK_EQ(m_axil_rdata, data);
    `CHECK_EQ(m_axil_rresp, 2'b00);

    `TICK(clk);
    `CHECK_FALSE(m_axil_bvalid);
    `CHECK_FALSE(m_axil_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_sram_if_tbi);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_io);

  `TEST_SUITE_END();

endmodule
