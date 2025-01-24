`include "svc_unit.sv"

`include "svc_axi_stripe_rd.sv"
`include "svc_axi_mem.sv"

// This is just a quick smoke test. The real testing is via formal of the
// combined rw module.

module svc_axi_stripe_rd_tb;
  parameter NUM_S = 2;
  parameter AW = 8;
  parameter DW = 16;
  parameter IDW = 4;
  parameter SAW = AW - $clog2(NUM_S);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                      m_axi_arvalid;
  logic [  IDW-1:0]          m_axi_arid;
  logic [   AW-1:0]          m_axi_araddr;
  logic [      7:0]          m_axi_arlen;
  logic [      2:0]          m_axi_arsize;
  logic [      1:0]          m_axi_arburst;
  logic                      m_axi_arready;
  logic                      m_axi_rvalid;
  logic [  IDW-1:0]          m_axi_rid;
  // verilator lint_off: UNUSEDSIGNAL
  logic [   DW-1:0]          m_axi_rdata;
  // verilator lint_on: UNUSEDSIGNAL
  logic [      1:0]          m_axi_rresp;
  logic                      m_axi_rlast;
  logic                      m_axi_rready;

  logic [NUM_S-1:0]          s_axi_arvalid;
  logic [NUM_S-1:0][IDW-1:0] s_axi_arid;
  logic [NUM_S-1:0][SAW-1:0] s_axi_araddr;
  logic [NUM_S-1:0][    7:0] s_axi_arlen;
  logic [NUM_S-1:0][    2:0] s_axi_arsize;
  logic [NUM_S-1:0][    1:0] s_axi_arburst;
  logic [NUM_S-1:0]          s_axi_arready;
  logic [NUM_S-1:0]          s_axi_rvalid;
  logic [NUM_S-1:0][IDW-1:0] s_axi_rid;
  logic [NUM_S-1:0][ DW-1:0] s_axi_rdata;
  logic [NUM_S-1:0][    1:0] s_axi_rresp;
  logic [NUM_S-1:0]          s_axi_rlast;
  logic [NUM_S-1:0]          s_axi_rready;

  svc_axi_stripe_rd #(
      .NUM_S         (NUM_S),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

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

        .s_axi_awvalid(1'b0),
        .s_axi_awid   ('0),
        .s_axi_awaddr ('0),
        .s_axi_awlen  ('0),
        .s_axi_awsize ('0),
        .s_axi_awburst('0),
        .s_axi_awready(),
        .s_axi_wvalid (1'b0),
        .s_axi_wdata  ('0),
        .s_axi_wstrb  ('0),
        .s_axi_wlast  ('0),
        .s_axi_wready (),
        .s_axi_bvalid (),
        .s_axi_bid    (),
        .s_axi_bresp  (),
        .s_axi_bready (1'b0),

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
    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_arvalid <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  // Basic smoke test - note: we didn't init the memory, so this is really
  // just a basic bus test since we can't validate our responses
  task automatic test_basic;
    logic [ AW-1:0] addr = AW'(8'hA0);
    logic [IDW-1:0] id = IDW'(4'hD);

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
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_FALSE(m_axi_rlast);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_TRUE(m_axi_rlast);

    `TICK(clk);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_stripe_rd_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
