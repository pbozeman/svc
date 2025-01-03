`include "svc_unit.sv"

`include "svc_axi_sram_if.sv"
`include "svc_model_sram_if.sv"

module svc_axi_sram_if_tb;
  parameter AW = 16;
  parameter DW = 16;
  parameter IW = 4;
  parameter MW = IW;
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
  logic             sram_cmd_last;
  logic [   DW-1:0] sram_cmd_wr_data;
  logic [STRBW-1:0] sram_cmd_wr_strb;
  logic             sram_rd_resp_valid;
  logic             sram_rd_resp_ready;
  logic [   DW-1:0] sram_rd_resp_data;
  logic [   MW-1:0] sram_rd_resp_meta;
  logic             sram_rd_resp_last;

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
      .sram_cmd_last     (sram_cmd_last),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data),
      .sram_rd_resp_meta (sram_rd_resp_meta),
      .sram_rd_resp_last (sram_rd_resp_last)
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
      .sram_cmd_meta    (sram_cmd_meta),
      .sram_cmd_last    (sram_cmd_last),
      .sram_cmd_wr_en   (sram_cmd_wr_en),
      .sram_cmd_wr_data (sram_cmd_wr_data),
      .sram_cmd_wr_strb (sram_cmd_wr_strb),
      .sram_resp_valid  (sram_rd_resp_valid),
      .sram_resp_ready  (sram_rd_resp_ready),
      .sram_resp_meta   (sram_rd_resp_meta),
      .sram_resp_last   (sram_rd_resp_last),
      .sram_resp_rd_data(sram_rd_resp_data)
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
      m_axi_arlen   <= '0;
      m_axi_arsize  <= '0;
      m_axi_arburst <= '0;
      m_axi_rready  <= 1'b0;

      auto_valid    <= 1'b1;
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
      if (m_axi_awvalid && m_axi_awready) begin
        m_axi_awvalid <= 1'b0;
      end

      if (m_axi_arvalid && m_axi_arready) begin
        m_axi_arvalid <= 1'b0;
      end
    end
  end

  task test_initial;
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_bvalid);
    `CHECK_EQ(m_axi_bresp, '0);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  task automatic test_aw_only;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_FALSE(sram_cmd_valid);

    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_w_only;
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_FALSE(sram_cmd_valid);

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_EQ(sram_cmd_wr_strb, '1);
    `CHECK_FALSE(m_axi_bvalid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_aw_w_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_FALSE(sram_cmd_valid);
    m_axi_awvalid = 1'b1;
    m_axi_awid    = 4'hB;
    m_axi_awaddr  = addr;

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_bready = 1'b1;

    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_TRUE(sram_cmd_ready);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);
    `CHECK_EQ(sram_cmd_wr_strb, '1);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_TRUE(m_axi_bvalid);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_w_aw_delayed;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_FALSE(sram_cmd_valid);
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_bready = 1'b1;

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);

    m_axi_awvalid = 1'b1;
    m_axi_awid    = 4'hB;
    m_axi_awaddr  = addr;

    @(posedge clk);
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_TRUE(sram_cmd_ready);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_TRUE(m_axi_bvalid);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_FALSE(sram_cmd_valid);

    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;
    m_axi_awid    = 4'hB;
    m_axi_wvalid  = 1'b1;
    m_axi_wdata   = data;
    m_axi_wstrb   = '1;
    m_axi_bready  = 1'b1;

    repeat (3) begin
      @(posedge clk);
      `CHECK_TRUE(sram_cmd_valid);
      `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
      `CHECK_EQ(sram_cmd_wr_data, data);
      `CHECK_EQ(sram_cmd_wr_strb, '1);
      `CHECK_FALSE(m_axi_bvalid);
    end

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_TRUE(m_axi_bvalid);
    `CHECK_EQ(m_axi_bid, 4'hB);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic write_beats(logic [AW-1:0] addr, logic [DW-1:0] data);
    // this assumes a 16 bit bus, 4 beats

    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data;
    m_axi_wstrb  = '1;
    m_axi_wlast  = 1'b0;

    // first
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_wr_data, data);

    @(posedge clk);
    `CHECK_TRUE(m_axi_wready);

    // second
    m_axi_wdata = data + DW'(1);
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 2));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(1));

    @(posedge clk);
    `CHECK_TRUE(m_axi_wready);

    // third
    m_axi_wdata = data + DW'(2);
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 4));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(2));

    @(posedge clk);
    `CHECK_TRUE(m_axi_wready);

    // Fourth
    m_axi_wdata = data + DW'(3);
    m_axi_wlast = 1'b1;
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 6));
    `CHECK_EQ(sram_cmd_wr_data, data + DW'(3));
  endtask

  task automatic test_w_burst;
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

    @(posedge clk);
    `CHECK_TRUE(m_axi_awready && m_axi_awvalid);
    `CHECK_FALSE(sram_cmd_valid);

    write_beats(addr, data);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
  endtask

  task automatic test_r_axi_rready;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_FALSE(m_axi_rvalid);
    m_axi_arvalid = 1'b1;
    m_axi_arid    = 4'hB;
    m_axi_araddr  = addr;

    @(posedge clk);
    `CHECK_FALSE(m_axi_rvalid);
    `CHECK_FALSE(sram_rd_resp_ready);

    @(posedge clk);
    `CHECK_TRUE(m_axi_rvalid);
    `CHECK_EQ(m_axi_rid, 4'hB);
    `CHECK_EQ(m_axi_rdata, a_to_d(addr));
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(sram_rd_resp_ready);

    repeat (3) begin
      @(posedge clk);
      `CHECK_TRUE(m_axi_rvalid);
      `CHECK_EQ(m_axi_rid, 4'hB);
      `CHECK_EQ(m_axi_rdata, a_to_d(addr));
      `CHECK_EQ(m_axi_rresp, 2'b00);
      `CHECK_FALSE(sram_rd_resp_ready);
    end

    m_axi_rready = 1'b1;
    `CHECK_TRUE(sram_rd_resp_ready);
  endtask

  task automatic read_beats(logic [AW-1:0] addr);
    // this assumes a 16 bit bus, 4 beats

    // First beat
    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr));
    `CHECK_EQ(sram_cmd_meta, 4'hB);
    `CHECK_FALSE(sram_cmd_last);
    `CHECK_FALSE(m_axi_rvalid);

    // This is kinda janky, but in order to manage the valid signal
    // and do all the addr and data asserts, we enter this task in
    // different relative positions to the acceptance of the txn when
    // doing the back to back read tests.
    `CHECK_WAIT_FOR(clk, m_axi_rvalid);

    `CHECK_TRUE(m_axi_rvalid);
    `CHECK_EQ(m_axi_rdata, a_to_d(addr));
    `CHECK_EQ(m_axi_rid, 4'hB);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 2));
    `CHECK_EQ(sram_cmd_meta, 4'hB);
    `CHECK_FALSE(sram_cmd_last);

    @(posedge clk);
    `CHECK_TRUE(m_axi_rvalid);
    `CHECK_EQ(m_axi_rdata, a_to_d(addr + 2));
    `CHECK_EQ(m_axi_rid, 4'hB);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 4));
    `CHECK_EQ(sram_cmd_meta, 4'hB);
    `CHECK_FALSE(sram_cmd_last);

    @(posedge clk);
    `CHECK_TRUE(m_axi_rvalid);
    `CHECK_EQ(m_axi_rdata, a_to_d(addr + 4));
    `CHECK_EQ(m_axi_rid, 4'hB);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `CHECK_TRUE(sram_cmd_valid);
    `CHECK_EQ(sram_cmd_addr, a_to_sa(addr + 6));
    `CHECK_EQ(sram_cmd_meta, 4'hB);
    `CHECK_TRUE(sram_cmd_last);

    @(posedge clk);
    `CHECK_TRUE(m_axi_rvalid);
    `CHECK_EQ(m_axi_rdata, a_to_d(addr + 6));
    `CHECK_EQ(m_axi_rid, 4'hB);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_TRUE(m_axi_rlast);
  endtask

  task automatic test_r_burst;
    logic [AW-1:0] addr = AW'(16'hA000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr;
    m_axi_arid    = 4'hB;
    m_axi_arlen   = 8'h3;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;
    m_axi_rready  = 1'b1;

    auto_valid    = 1'b0;

    @(posedge clk);
    `CHECK_TRUE(m_axi_arready && m_axi_arvalid);
    m_axi_arvalid = 1'b0;
    read_beats(addr);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_rvalid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  task automatic test_r_r_burst;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [AW-1:0] addr1 = AW'(16'hB000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr0;
    m_axi_arid    = 4'hB;
    m_axi_arlen   = 8'h3;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;
    m_axi_rready  = 1'b1;

    auto_valid    = 1'b0;

    @(posedge clk);
    `CHECK_TRUE(m_axi_arready && m_axi_arvalid);
    m_axi_araddr = addr1;
    auto_valid   = 1'b1;
    read_beats(addr0);

    @(posedge clk);
    read_beats(addr1);
    `CHECK_TRUE(m_axi_rvalid);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_rvalid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  task automatic test_r_w_burst;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [AW-1:0] addr1 = AW'(16'hB000);
    logic [DW-1:0] data1 = DW'(16'hD000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr0;
    m_axi_arid    = 4'hB;
    m_axi_arlen   = 8'h3;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;
    m_axi_rready  = 1'b1;


    @(posedge clk);
    `CHECK_TRUE(m_axi_arready && m_axi_arvalid);
    // switch to write
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr1;
    m_axi_awid    = 4'hB;
    m_axi_awlen   = 8'h3;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;
    m_axi_bready  = 1'b1;

    read_beats(addr0);

    @(posedge clk);
    // the write was accepted back while reading beats, so we should be able
    // to just go.
    write_beats(addr1, data1);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_rvalid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_w_r_burst;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [DW-1:0] data0 = DW'(16'hD000);
    logic [AW-1:0] addr1 = AW'(16'hB000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr0;
    m_axi_awid    = 4'hB;
    m_axi_awlen   = 8'h3;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;
    m_axi_bready  = 1'b1;

    @(posedge clk);
    // switch to read
    #0;
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr1;
    m_axi_arid    = 4'hB;
    m_axi_arlen   = 8'h3;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;
    m_axi_rready  = 1'b1;

    write_beats(addr0, data0);

    // the read was accepted back while reading beats, so we should be able
    // to just go.
    @(posedge clk);
    read_beats(addr1);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);
    `CHECK_FALSE(m_axi_rvalid);
    `CHECK_FALSE(m_axi_bvalid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_rvalid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  task automatic test_w_w_burst;
    logic [AW-1:0] addr0 = AW'(16'hA000);
    logic [DW-1:0] data0 = DW'(16'hD000);
    logic [AW-1:0] addr1 = AW'(16'hB000);
    logic [DW-1:0] data1 = DW'(16'hE000);

    // Length of 4 (N-1)
    // INCR burst
    // 2 bytes (16 bits)
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr0;
    m_axi_awid    = 4'hB;
    m_axi_awlen   = 8'h3;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;
    m_axi_bready  = 1'b1;

    auto_valid    = 1'b0;

    `CHECK_TRUE(m_axi_awvalid && m_axi_awready);
    @(posedge clk);
    #0;
    // don't drop valid, write back to back
    // let valid drop again when accepted
    m_axi_awaddr = addr1;
    auto_valid   = 1'b1;

    @(posedge clk);
    write_beats(addr0, data0);

    // TODO: remove this idle transition state
    @(posedge clk);
    @(posedge clk);
    write_beats(addr1, data1);

    @(posedge clk);
    `CHECK_FALSE(sram_cmd_valid);

    @(posedge clk);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_sram_if_tb);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_aw_only);
  `TEST_CASE(test_w_only);
  `TEST_CASE(test_aw_w_delayed);
  `TEST_CASE(test_w_aw_delayed);
  `TEST_CASE(test_w_burst);

  `TEST_CASE(test_r_axi_rready);
  `TEST_CASE(test_r_burst);

  `TEST_CASE(test_r_r_burst);
  `TEST_CASE(test_r_w_burst);
  `TEST_CASE(test_w_r_burst);
  `TEST_CASE(test_w_w_burst);

  `TEST_SUITE_END();

endmodule
