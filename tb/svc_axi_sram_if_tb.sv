`include "svc_unit.sv"

`include "svc_axi_sram_if.sv"
`include "svc_model_sram.sv"

// verilator lint_off: UNUSEDSIGNAL
// verilator lint_off: UNDRIVEN
module svc_axi_sram_if_tb;
  parameter AW = 16;
  parameter DW = 16;
  parameter IW = 4;
  parameter MW = IW + 1;
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
  logic             m_axi_wvalid;
  logic             m_axi_wready;
  logic [   DW-1:0] m_axi_wdata;
  logic [STRBW-1:0] m_axi_wstrb;
  logic             m_axi_wlast;
  logic             m_axi_bvalid;
  logic             m_axi_bready;
  logic [   IW-1:0] m_axi_bid;
  logic [      1:0] m_axi_bresp;

  logic             m_axi_arvalid;
  logic             m_axi_arready;
  logic [   IW-1:0] m_axi_arid;
  logic [   AW-1:0] m_axi_araddr;
  logic [      7:0] m_axi_arlen;
  logic [      2:0] m_axi_arsize;
  logic [      1:0] m_axi_arburst;
  logic             m_axi_rvalid;
  logic             m_axi_rready;
  logic [   IW-1:0] m_axi_rid;
  logic [   DW-1:0] m_axi_rdata;
  logic [      1:0] m_axi_rresp;
  logic             m_axi_rlast;

  logic             sram_cmd_valid;
  logic             sram_cmd_ready;
  logic             sram_cmd_wr_en;
  logic [  SAW-1:0] sram_cmd_addr;
  logic [   MW-1:0] sram_cmd_meta;
  logic [   DW-1:0] sram_cmd_wr_data;
  logic [STRBW-1:0] sram_cmd_wr_strb;
  logic             sram_rd_resp_valid;
  logic             sram_rd_resp_ready;
  logic [   DW-1:0] sram_rd_resp_data;
  logic [   MW-1:0] sram_rd_resp_meta;

  // if true, test cases don't have to manage dropping valid signals
  logic             auto_valid;

  svc_axi_sram_if #(
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

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arready(m_axi_arready),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rready (m_axi_rready),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),

      .sram_cmd_valid    (sram_cmd_valid),
      .sram_cmd_ready    (sram_cmd_ready),
      .sram_cmd_addr     (sram_cmd_addr),
      .sram_cmd_meta     (sram_cmd_meta),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data),
      .sram_rd_resp_meta (sram_rd_resp_meta)
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
      .sram_cmd_meta     (sram_cmd_meta),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data),
      .sram_rd_resp_meta (sram_rd_resp_meta)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awaddr  <= '0;
      m_axi_awvalid <= 1'b0;
      m_axi_wdata   <= '0;
      m_axi_wstrb   <= '0;
      m_axi_wvalid  <= 1'b0;
      m_axi_bready  <= 1'b0;
      m_axi_arvalid <= 1'b0;
      m_axi_araddr  <= '0;
      m_axi_rready  <= 1'b0;

      auto_valid    <= 1'b1;
    end
  end

  // used in assertions with data returned by the fake sram above
  function logic [DW-1:0] a_to_d(logic [AW-1:0] addr);
    return DW'(addr[AW-1:LSB]);
  endfunction

  function logic [SAW-1:0] a_to_sa(logic [AW-1:0] addr);
    return SAW'(addr[AW-1:LSB]);
  endfunction

  // clear m valid flags on txn acceptance
  always_ff @(posedge clk) begin
    if (auto_valid) begin
      if (m_axi_awvalid && m_axi_awready) begin
        m_axi_awvalid <= 1'b0;
      end

      if (m_axi_wvalid && m_axi_wready) begin
        m_axi_wvalid <= 1'b0;
      end

      if (m_axi_arvalid && m_axi_arready) begin
        m_axi_arvalid <= 1'b0;
      end
    end
  end

  task test_initial;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
    `CHECK_EQ(m_axi_bresp, '0);
    `CHECK_EQ(m_axi_rvalid, 1'b0);
  endtask

  task automatic test_aw_only;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_w_only;
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_EQ(sram_cmd_wr_strb, '1);
    `CHECK_EQ(m_axi_bvalid, 1'b0);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_aw_w_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);
    m_axi_awvalid = 1'b1;
    m_axi_awid    = 4'hB;
    m_axi_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_bready = 1'b1;

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_ready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_EQ(sram_cmd_wr_strb, '1);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_w_aw_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_bready = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    m_axi_awvalid = 1'b1;
    m_axi_awid    = 4'hB;
    m_axi_awaddr  = addr;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_ready, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_cmd_valid, 1'b0);

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
      `CHECK_EQ(sram_cmd_valid, 1'b1);
      `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
      `CHECK_EQ(sram_cmd_wr_data, data);
      `CHECK_EQ(sram_cmd_wr_strb, '1);
      `CHECK_EQ(m_axi_bvalid, 1'b0);
    end

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  task automatic test_burst;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;
    m_axi_awid    = 4'hB;
    m_axi_awlen   = 8'h3;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;
    m_axi_bready  = 1'b1;

    auto_valid    = 1'b0;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);

    // First beat
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_wlast  = 1'b0;

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);

    // Second beat
    @(posedge clk);
    m_axi_wdata = data + DW'(1);

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 2));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(1));

    // Third beat
    @(posedge clk);
    m_axi_wdata = data + DW'(2);

    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 4));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(2));

    // Fourth and last beat
    m_axi_wdata = data + DW'(3);
    m_axi_wlast = 1'b1;

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b1);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 6));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(3));

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_bvalid, 1'b1);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    #1;
    `CHECK_EQ(m_axi_bvalid, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_sram_if_tb);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_aw_only);
  `TEST_CASE(test_w_only);
  `TEST_CASE(test_aw_w_delayed);
  `TEST_CASE(test_w_aw_delayed);
  `TEST_CASE(test_burst);

  // TODO: read tests

  `TEST_SUITE_END();

endmodule
