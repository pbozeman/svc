`include "svc_unit.sv"

`include "svc_axil_sram_if.sv"
`include "svc_model_sram.sv"

module svc_axil_sram_if_tb;
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
  logic             sram_rd_resp_valid;
  logic             sram_rd_resp_ready;
  logic [   DW-1:0] sram_rd_resp_data;

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
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data)
  );

  svc_model_sram #(
      .UNITIALIZED_READS_OK(1),
      .SRAM_ADDR_WIDTH     (SAW),
      .SRAM_DATA_WIDTH     (DW)
  ) svc_model_sram_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid    (sram_cmd_valid),
      .sram_cmd_ready    (sram_cmd_ready),
      .sram_cmd_addr     (sram_cmd_addr),
      .sram_cmd_meta     (),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data),
      .sram_rd_resp_meta ()
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

  task test_initial;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axil_bvalid, 1'b0);
    `CHECK_EQ(m_axil_bresp, '0);
    `CHECK_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_aw_only;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
  endtask

  task automatic test_w_only;
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_wvalid = 1'b1;
    m_axil_wdata  = data;
    m_axil_wstrb  = '1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
  endtask

  task automatic test_aw_w_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_wvalid = 1'b1;
    m_axil_wdata  = data;
    m_axil_wstrb  = '1;

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_ready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_EQ(sram_cmd_wr_strb, '1);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
  endtask

  task automatic test_w_aw_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_wvalid = 1'b1;
    m_axil_wdata  = data;
    m_axil_wstrb  = '1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr;

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_ready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
  endtask

  task automatic test_r_axi_rready;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_EQ(m_axil_rvalid, 1'b0);
    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr;
    `CHECK_EQ(m_axil_rresp, 2'b00);

    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b0);
    `CHECK_EQ(sram_rd_resp_ready, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b1);
    `CHECK_EQ(m_axil_rdata, a_to_d(addr));
    `CHECK_EQ(sram_rd_resp_ready, 1'b0);
    `CHECK_EQ(m_axil_rresp, 2'b00);

    repeat (3) begin
      @(posedge clk);
      `CHECK_EQ(m_axil_rvalid, 1'b1);
      `CHECK_EQ(m_axil_rdata, a_to_d(addr));
      `CHECK_EQ(m_axil_rresp, 2'b00);
      `CHECK_EQ(sram_rd_resp_ready, 1'b0);
    end

    m_axil_rready = 1'b1;
    `CHECK_EQ(sram_rd_resp_ready, 1'b1);
  endtask

  task automatic test_r_r;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [AW-1:0] addr1 = AW'(16'hB000);

    auto_valid     = 1'b0;

    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr0;
    m_axil_rready  = 1'b1;
    m_axil_rready  = 1'b1;

    #1;
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr0));
    `CHECK_EQ(m_axil_rvalid, 1'b0);

    @(posedge clk);
    // don't drop valid, read back to back
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    m_axil_araddr = addr1;
    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b1);
    `CHECK_EQ(m_axil_rdata, a_to_d(addr0));
    `CHECK_EQ(m_axil_rresp, 2'b00);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr1));

    @(posedge clk);
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    m_axil_arvalid = 1'b0;
    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b1);
    `CHECK_EQ(m_axil_rdata, a_to_d(addr1));
    `CHECK_EQ(m_axil_rresp, 2'b00);
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_r_w;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [AW-1:0] addr1 = AW'(16'hB000);
    logic [DW-1:0] data1 = DW'(16'hBABE);

    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr0;
    m_axil_rready  = 1'b1;

    #1;
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr0));
    `CHECK_EQ(m_axil_rvalid, 1'b0);

    @(posedge clk);
    // switch to write
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr1;
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = data1;
    m_axil_bready  = 1'b1;
    #1;
    `CHECK_EQ(m_axil_rvalid, 1'b1);
    `CHECK_EQ(m_axil_rdata, a_to_d(addr0));
    `CHECK_EQ(m_axil_rresp, 2'b00);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr1));
    `CHECK_EQ(sram_cmd_wr_data, data1);
    `CHECK_EQ(sram_cmd_wr_en, 1'b1);

    @(posedge clk);
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b1);
    `CHECK_EQ(m_axil_rvalid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b0);
    `CHECK_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_w_r;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [DW-1:0] data0 = DW'(16'hBABE);
    logic [AW-1:0] addr1 = AW'(16'hB000);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr0;
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = data0;
    m_axil_bready  = 1'b1;

    #1;
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    `CHECK_EQ(m_axil_wvalid && m_axil_wready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr0));
    `CHECK_EQ(sram_cmd_wr_data, data0);
    `CHECK_EQ(sram_cmd_wr_en, 1'b1);

    @(posedge clk);
    // switch to read
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    `CHECK_EQ(m_axil_wvalid && m_axil_wready, 1'b1);

    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr1;
    m_axil_rready  = 1'b1;

    #1;
    `CHECK_EQ(m_axil_arvalid && m_axil_arready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr1));
    `CHECK_EQ(m_axil_bvalid, 1'b1);
    `CHECK_EQ(m_axil_rvalid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b0);
    `CHECK_EQ(m_axil_rvalid, 1'b1);
    `CHECK_EQ(m_axil_rresp, 2'b00);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b0);
    `CHECK_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_w_w;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [DW-1:0] data0 = DW'(16'hBABE);
    logic [AW-1:0] addr1 = AW'(16'hB000);
    logic [AW-1:0] data1 = AW'(16'hCAFE);

    auto_valid     = 1'b0;

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr0;
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = data0;
    m_axil_bready  = 1'b1;

    #1;
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    `CHECK_EQ(m_axil_wvalid && m_axil_wready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr0));
    `CHECK_EQ(sram_cmd_wr_data, data0);
    `CHECK_EQ(sram_cmd_wr_en, 1'b1);

    @(posedge clk);
    // don't drop valid, write back to back
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    `CHECK_EQ(m_axil_wvalid && m_axil_wready, 1'b1);

    m_axil_awaddr = addr1;
    m_axil_wdata  = data1;

    #1;
    `CHECK_EQ(m_axil_awvalid && m_axil_awready, 1'b1);
    `CHECK_EQ(m_axil_wvalid && m_axil_wready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr1));
    `CHECK_EQ(sram_cmd_wr_en, 1'b1);
    `CHECK_EQ(m_axil_bvalid, 1'b1);

    @(posedge clk);
    m_axil_awvalid = 1'b0;
    m_axil_wvalid  = 1'b0;
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b1);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axil_bvalid, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_sram_if_tb);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_aw_only);
  `TEST_CASE(test_w_only);
  `TEST_CASE(test_aw_w_delayed);
  `TEST_CASE(test_w_aw_delayed);
  `TEST_CASE(test_r_axi_rready);
  `TEST_CASE(test_r_r);
  `TEST_CASE(test_r_w);
  `TEST_CASE(test_w_r);
  `TEST_CASE(test_w_w);

  `TEST_SUITE_END();

endmodule
