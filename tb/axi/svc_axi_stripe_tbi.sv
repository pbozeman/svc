`include "svc_unit.sv"

`include "svc_axi_stripe.sv"
`include "svc_axi_mem.sv"

// This is just a quick smoke test. The real testing is via formal.
module svc_axi_stripe_tbi;
  parameter NUM_S = 2;
  parameter AW = 8;
  parameter DW = 16;
  parameter IDW = 4;
  parameter SAW = AW - $clog2(NUM_S);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                       m_axi_awvalid;
  logic [  IDW-1:0]           m_axi_awid;
  logic [   AW-1:0]           m_axi_awaddr;
  logic [      7:0]           m_axi_awlen;
  logic [      2:0]           m_axi_awsize;
  logic [      1:0]           m_axi_awburst;
  logic                       m_axi_awready;
  logic                       m_axi_wvalid;
  logic [   DW-1:0]           m_axi_wdata;
  logic [ DW/8-1:0]           m_axi_wstrb;
  logic                       m_axi_wlast;
  logic                       m_axi_wready;
  logic                       m_axi_bvalid;
  logic [  IDW-1:0]           m_axi_bid;
  logic [      1:0]           m_axi_bresp;
  logic                       m_axi_bready;

  logic                       m_axi_arvalid;
  logic [  IDW-1:0]           m_axi_arid;
  logic [   AW-1:0]           m_axi_araddr;
  logic [      7:0]           m_axi_arlen;
  logic [      2:0]           m_axi_arsize;
  logic [      1:0]           m_axi_arburst;
  logic                       m_axi_arready;
  logic                       m_axi_rvalid;
  logic [  IDW-1:0]           m_axi_rid;
  logic [   DW-1:0]           m_axi_rdata;
  logic [      1:0]           m_axi_rresp;
  logic                       m_axi_rlast;
  logic                       m_axi_rready;

  logic [NUM_S-1:0]           s_axi_awvalid;
  logic [NUM_S-1:0][ IDW-1:0] s_axi_awid;
  logic [NUM_S-1:0][ SAW-1:0] s_axi_awaddr;
  logic [NUM_S-1:0][     7:0] s_axi_awlen;
  logic [NUM_S-1:0][     2:0] s_axi_awsize;
  logic [NUM_S-1:0][     1:0] s_axi_awburst;
  logic [NUM_S-1:0]           s_axi_awready;
  logic [NUM_S-1:0]           s_axi_wvalid;
  logic [NUM_S-1:0][  DW-1:0] s_axi_wdata;
  logic [NUM_S-1:0][DW/8-1:0] s_axi_wstrb;
  logic [NUM_S-1:0]           s_axi_wlast;
  logic [NUM_S-1:0]           s_axi_wready;
  logic [NUM_S-1:0]           s_axi_bvalid;
  logic [NUM_S-1:0][ IDW-1:0] s_axi_bid;
  logic [NUM_S-1:0][     1:0] s_axi_bresp;
  logic [NUM_S-1:0]           s_axi_bready;

  logic [NUM_S-1:0]           s_axi_arvalid;
  logic [NUM_S-1:0][ IDW-1:0] s_axi_arid;
  logic [NUM_S-1:0][ SAW-1:0] s_axi_araddr;
  logic [NUM_S-1:0][     7:0] s_axi_arlen;
  logic [NUM_S-1:0][     2:0] s_axi_arsize;
  logic [NUM_S-1:0][     1:0] s_axi_arburst;
  logic [NUM_S-1:0]           s_axi_arready;
  logic [NUM_S-1:0]           s_axi_rvalid;
  logic [NUM_S-1:0][ IDW-1:0] s_axi_rid;
  logic [NUM_S-1:0][  DW-1:0] s_axi_rdata;
  logic [NUM_S-1:0][     1:0] s_axi_rresp;
  logic [NUM_S-1:0]           s_axi_rlast;
  logic [NUM_S-1:0]           s_axi_rready;

  svc_axi_stripe #(
      .NUM_S         (NUM_S),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awready(m_axi_awready),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bready (m_axi_bready),

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),
      .s_axi_rready (m_axi_rready),

      .m_axi_awvalid(s_axi_awvalid),
      .m_axi_awid   (s_axi_awid),
      .m_axi_awaddr (s_axi_awaddr),
      .m_axi_awlen  (s_axi_awlen),
      .m_axi_awsize (s_axi_awsize),
      .m_axi_awburst(s_axi_awburst),
      .m_axi_awready(s_axi_awready),
      .m_axi_wvalid (s_axi_wvalid),
      .m_axi_wdata  (s_axi_wdata),
      .m_axi_wstrb  (s_axi_wstrb),
      .m_axi_wlast  (s_axi_wlast),
      .m_axi_wready (s_axi_wready),
      .m_axi_bvalid (s_axi_bvalid),
      .m_axi_bid    (s_axi_bid),
      .m_axi_bresp  (s_axi_bresp),
      .m_axi_bready (s_axi_bready),

      .m_axi_arvalid(s_axi_arvalid),
      .m_axi_arid   (s_axi_arid),
      .m_axi_araddr (s_axi_araddr),
      .m_axi_arlen  (s_axi_arlen),
      .m_axi_arsize (s_axi_arsize),
      .m_axi_arburst(s_axi_arburst),
      .m_axi_arready(s_axi_arready),
      .m_axi_rvalid (s_axi_rvalid),
      .m_axi_rid    (s_axi_rid),
      .m_axi_rdata  (s_axi_rdata),
      .m_axi_rresp  (s_axi_rresp),
      .m_axi_rlast  (s_axi_rlast),
      .m_axi_rready (s_axi_rready)
  );

  for (genvar i = 0; i < NUM_S; i++) begin : gen_axi_mem
    svc_axi_mem #(
        .AXI_ADDR_WIDTH(SAW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH  (IDW)
    ) svc_axi_mem_i (
        .clk  (clk),
        .rst_n(rst_n),

        .s_axi_awvalid(s_axi_awvalid[i]),
        .s_axi_awid   (s_axi_awid[i]),
        .s_axi_awaddr (s_axi_awaddr[i]),
        .s_axi_awlen  (s_axi_awlen[i]),
        .s_axi_awsize (s_axi_awsize[i]),
        .s_axi_awburst(s_axi_awburst[i]),
        .s_axi_awready(s_axi_awready[i]),
        .s_axi_wvalid (s_axi_wvalid[i]),
        .s_axi_wdata  (s_axi_wdata[i]),
        .s_axi_wstrb  (s_axi_wstrb[i]),
        .s_axi_wlast  (s_axi_wlast[i]),
        .s_axi_wready (s_axi_wready[i]),
        .s_axi_bvalid (s_axi_bvalid[i]),
        .s_axi_bid    (s_axi_bid[i]),
        .s_axi_bresp  (s_axi_bresp[i]),
        .s_axi_bready (s_axi_bready[i]),

        .s_axi_arvalid(s_axi_arvalid[i]),
        .s_axi_arid   (s_axi_arid[i]),
        .s_axi_araddr (s_axi_araddr[i]),
        .s_axi_arlen  (s_axi_arlen[i]),
        .s_axi_arsize (s_axi_arsize[i]),
        .s_axi_arburst(s_axi_arburst[i]),
        .s_axi_arready(s_axi_arready[i]),
        .s_axi_rvalid (s_axi_rvalid[i]),
        .s_axi_rid    (s_axi_rid[i]),
        .s_axi_rdata  (s_axi_rdata[i]),
        .s_axi_rresp  (s_axi_rresp[i]),
        .s_axi_rlast  (s_axi_rlast[i]),
        .s_axi_rready (s_axi_rready[i])
    );
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awvalid <= 1'b0;
      m_axi_awid    <= 0;
      m_axi_awaddr  <= 0;
      m_axi_awlen   <= 0;
      m_axi_awsize  <= 0;
      m_axi_awburst <= 0;

      m_axi_wvalid  <= 1'b0;
      m_axi_wdata   <= 0;
      m_axi_wstrb   <= 0;
      m_axi_wlast   <= 0;

      m_axi_bready  <= 1'b0;

      m_axi_arvalid <= 1'b0;
      m_axi_arid    <= 0;
      m_axi_araddr  <= 0;
      m_axi_arlen   <= 0;
      m_axi_arsize  <= 0;
      m_axi_arburst <= 0;

      m_axi_rready  <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_awvalid && m_axi_awready) begin
      m_axi_awvalid <= 1'b0;
    end

    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_arvalid <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
    `CHECK_FALSE(m_axi_bvalid);

    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  task automatic test_basic;
    logic [ AW-1:0] addr = AW'(8'hA0);
    logic [ DW-1:0] data = DW'(16'hD000);
    logic [IDW-1:0] id = IDW'(4'hD);

    // arlen is 4, and NUM_S is 2, so this should write to each sub twice
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;
    m_axi_awid    = id;
    m_axi_awlen   = 8'h03;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;

    m_axi_bready  = 1'b1;

    // Send first data beat
    m_axi_wvalid  = 1'b1;
    m_axi_wdata   = data;
    m_axi_wstrb   = '1;
    m_axi_wlast   = 1'b0;
    `CHECK_WAIT_FOR(clk, m_axi_wvalid && m_axi_wready);
    `CHECK_FALSE(m_axi_bvalid);
    `TICK(clk);

    // Second
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data + DW'(1);
    m_axi_wlast  = 1'b0;
    `CHECK_WAIT_FOR(clk, m_axi_wvalid && m_axi_wready);
    `CHECK_FALSE(m_axi_bvalid);
    `TICK(clk);

    // Thrid
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data + DW'(2);
    m_axi_wlast  = 1'b0;
    `CHECK_WAIT_FOR(clk, m_axi_wvalid && m_axi_wready);
    `CHECK_FALSE(m_axi_bvalid);
    `TICK(clk);

    // Forth
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data + DW'(3);
    m_axi_wlast  = 1'b1;
    `CHECK_WAIT_FOR(clk, m_axi_wvalid && m_axi_wready);
    `CHECK_FALSE(m_axi_bvalid);
    `TICK(clk);
    m_axi_wvalid = 1'b0;

    // TODO: there is a cycle of latency on the bresp that could be optimized
    // out. (1 cycle is here because wr is pipelined, then 1 more cycle for
    // bvalid)
    `CHECK_WAIT_FOR(clk, m_axi_bvalid, 2);
    `CHECK_EQ(m_axi_bid, id);
    `CHECK_EQ(m_axi_bresp, 2'b00);

    `TICK(clk);
    `CHECK_FALSE(m_axi_bvalid);

    //
    // Read it back
    //

    // arlen is 4, and NUM_S is 2, so this should read from each sub twice
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr;
    m_axi_arid    = id;
    m_axi_arlen   = 8'h03;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;

    m_axi_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rdata, data);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rdata, data + DW'(1));
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rdata, data + DW'(2));
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rdata, data + DW'(3));
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_TRUE(m_axi_rlast);

    `TICK(clk);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_stripe_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
