`include "svc_unit.sv"

`include "svc_axi_sram_if_wr.sv"

module svc_axi_sram_if_wr_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IW = 4;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;
  parameter STRBW = (DW / 8);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic             m_axi_awvalid;
  logic             m_axi_awready;
  logic [   IW-1:0] m_axi_awid;
  logic [   AW-1:0] m_axi_awaddr;
  logic [      7:0] m_axi_awlen;
  logic [      2:0] m_axi_awsize;
  logic [      1:0] m_axi_awburst;
  logic [   DW-1:0] m_axi_wdata;
  logic [STRBW-1:0] m_axi_wstrb;
  logic             m_axi_wvalid;
  logic             m_axi_wready;
  logic             m_axi_wlast;
  logic [      1:0] m_axi_bresp;
  logic             m_axi_bvalid;
  logic             m_axi_bready;
  logic [   IW-1:0] m_axi_bid;

  logic             sram_wr_cmd_valid;
  logic             sram_wr_cmd_ready;
  logic [  SAW-1:0] sram_wr_cmd_addr;
  logic [   DW-1:0] sram_wr_cmd_data;
  logic [STRBW-1:0] sram_wr_cmd_strb;

  svc_axi_sram_if_wr #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awready(m_axi_awready),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wready (m_axi_wready),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bready (m_axi_bready),
      .s_axi_bid    (m_axi_bid),

      .sram_wr_cmd_valid(sram_wr_cmd_valid),
      .sram_wr_cmd_ready(sram_wr_cmd_ready),
      .sram_wr_cmd_addr (sram_wr_cmd_addr),
      .sram_wr_cmd_data (sram_wr_cmd_data),
      .sram_wr_cmd_strb (sram_wr_cmd_strb)
  );

  function automatic logic [SAW-1:0] a_to_sa(logic [AW-1:0] addr);
    // verilator lint_off: UNUSEDSIGNAL
    logic unused = |addr;
    // verilator lint_on: UNUSEDSIGNAL
    return SAW'(addr[AW-1:LSB]);
  endfunction

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awid        <= '0;
      m_axi_awaddr      <= '0;
      m_axi_awvalid     <= 1'b0;
      m_axi_awlen       <= '0;
      m_axi_awsize      <= '0;
      m_axi_awburst     <= '0;
      m_axi_wdata       <= '0;
      m_axi_wstrb       <= '0;
      m_axi_wlast       <= 1'b0;
      m_axi_wvalid      <= 1'b0;
      m_axi_bready      <= 1'b0;

      sram_wr_cmd_ready <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_awvalid && m_axi_awready) begin
      m_axi_awvalid <= 1'b0;
    end
  end

  task test_initial;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
    `CHECK_EQ(m_axi_bresp, '0);
  endtask

  task automatic test_aw_only;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axi_awvalid     = 1'b1;
    m_axi_awaddr      = addr;
    sram_wr_cmd_ready = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_w_only;
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axi_wvalid      = 1'b1;
    m_axi_wdata       = data;
    m_axi_wstrb       = '1;
    sram_wr_cmd_ready = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(sram_wr_cmd_data, data);
    `CHECK_EQ(sram_wr_cmd_strb, '1);
    `CHECK_EQ(m_axi_bvalid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_aw_w_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    sram_wr_cmd_ready = 1'b1;

    m_axi_awvalid     = 1'b1;
    m_axi_awid        = 4'hB;
    m_axi_awaddr      = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_bready = 1'b1;

    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_ready, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_wr_cmd_data, data);
    `CHECK_EQ(sram_wr_cmd_strb, '1);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_w_aw_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    sram_wr_cmd_ready = 1'b1;

    m_axi_wvalid      = 1'b1;
    m_axi_wdata       = data;
    m_axi_wstrb       = '1;
    m_axi_bready      = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axi_awvalid = 1'b1;
    m_axi_awid    = 4'hB;
    m_axi_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_ready, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_wr_cmd_data, data);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;
    m_axi_awid    = 4'hB;
    m_axi_wvalid  = 1'b1;
    m_axi_wdata   = data;
    m_axi_wstrb   = '1;
    m_axi_bready  = 1'b1;

    repeat (3) begin
      @(posedge clk);
      #1;
      `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
      `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr));
      `CHECK_EQ(sram_wr_cmd_data, data);
      `CHECK_EQ(sram_wr_cmd_strb, '1);
      `CHECK_EQ(m_axi_bvalid, 1'b0);
    end

    sram_wr_cmd_ready = 1'b1;
    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_burst;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_awvalid     = 1'b1;
    m_axi_awaddr      = addr;
    m_axi_awid        = 4'hB;
    m_axi_awlen       = 8'h3;
    m_axi_awburst     = 2'b01;
    m_axi_awsize      = 3'b001;
    sram_wr_cmd_ready = 1'b1;
    m_axi_bready      = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    // First beat
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_wlast  = 1'b0;

    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_wr_cmd_data, data);
    `CHECK_EQ(m_axi_wready, 1'b1);

    // Second beat
    @(posedge clk);
    m_axi_wdata = data + DW'(1);

    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr + 2));
    `CHECK_EQ(sram_wr_cmd_data, data + DW'(1));
    `CHECK_EQ(m_axi_wready, 1'b1);

    // Third beat
    @(posedge clk);
    m_axi_wdata = data + DW'(2);

    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr + 4));
    `CHECK_EQ(sram_wr_cmd_data, data + DW'(2));
    `CHECK_EQ(m_axi_wready, 1'b1);

    // Fourth and last beat
    m_axi_wdata = data + DW'(3);
    m_axi_wlast = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
    `CHECK_EQ(sram_wr_cmd_addr, a_to_sa(addr + 6));
    `CHECK_EQ(sram_wr_cmd_data, data + DW'(3));
    `CHECK_EQ(m_axi_wready, 1'b1);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_sram_if_wr_tb);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_aw_only);
  `TEST_CASE(test_w_only);
  `TEST_CASE(test_aw_w_delayed);
  `TEST_CASE(test_w_aw_delayed);
  `TEST_CASE(test_sram_ready);
  `TEST_CASE(test_burst);

  `TEST_SUITE_END();

endmodule
