`include "svc_unit.sv"
`include "svc_axil_router.sv"

// each of the _rd and _wr submodules do more testing, and this is tested
// again with formal verification. This TB is really just to ensure that the
// top level module can be synthesized.
//
// verilator lint_off: UNUSEDSIGNAL
module svc_axil_router_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Keep M/S different to catch bad types and/or casts.
  localparam M_AXIL_ADDR_WIDTH = 30;
  localparam M_AXIL_DATA_WIDTH = 32;

  localparam S_AXIL_ADDR_WIDTH = M_AXIL_ADDR_WIDTH - 4;
  localparam S_AXIL_DATA_WIDTH = M_AXIL_DATA_WIDTH - 8;

  localparam NUM_S = 3;

  // Manager interface signals
  logic                                                    m_axil_awvalid;
  logic [  M_AXIL_ADDR_WIDTH-1:0]                          m_axil_awaddr;
  logic                                                    m_axil_awready;

  logic                                                    m_axil_wvalid;
  logic [  M_AXIL_DATA_WIDTH-1:0]                          m_axil_wdata;
  logic [M_AXIL_DATA_WIDTH/8-1:0]                          m_axil_wstrb;
  logic                                                    m_axil_wready;

  logic                                                    m_axil_bvalid;
  logic [                    1:0]                          m_axil_bresp;
  logic                                                    m_axil_bready;

  logic                                                    m_axil_arvalid;
  logic [  M_AXIL_ADDR_WIDTH-1:0]                          m_axil_araddr;
  logic                                                    m_axil_arready;

  logic                                                    m_axil_rvalid;
  logic [  M_AXIL_DATA_WIDTH-1:0]                          m_axil_rdata;
  logic [                    1:0]                          m_axil_rresp;
  logic                                                    m_axil_rready;

  // Subordinate interface signals
  logic [              NUM_S-1:0]                          s_axil_awvalid;
  logic [              NUM_S-1:0][  S_AXIL_ADDR_WIDTH-1:0] s_axil_awaddr;
  logic [              NUM_S-1:0]                          s_axil_awready;

  logic [              NUM_S-1:0]                          s_axil_wvalid;
  logic [              NUM_S-1:0][  S_AXIL_DATA_WIDTH-1:0] s_axil_wdata;
  logic [              NUM_S-1:0][S_AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb;
  logic [              NUM_S-1:0]                          s_axil_wready;

  logic [              NUM_S-1:0]                          s_axil_bvalid;
  logic [              NUM_S-1:0][                    1:0] s_axil_bresp;
  logic [              NUM_S-1:0]                          s_axil_bready;

  logic [              NUM_S-1:0]                          s_axil_arvalid;
  logic [              NUM_S-1:0][  S_AXIL_ADDR_WIDTH-1:0] s_axil_araddr;
  logic [              NUM_S-1:0]                          s_axil_arready;

  logic [              NUM_S-1:0]                          s_axil_rvalid;
  logic [              NUM_S-1:0][  S_AXIL_DATA_WIDTH-1:0] s_axil_rdata;
  logic [              NUM_S-1:0][                    1:0] s_axil_rresp;
  logic [              NUM_S-1:0]                          s_axil_rready;

  svc_axil_router #(
      .S_AXIL_ADDR_WIDTH(M_AXIL_ADDR_WIDTH),
      .S_AXIL_DATA_WIDTH(M_AXIL_DATA_WIDTH),
      .M_AXIL_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .M_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .NUM_S            (NUM_S)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awvalid(m_axil_awvalid),
      .s_axil_awaddr (m_axil_awaddr),
      .s_axil_awready(m_axil_awready),

      .s_axil_wvalid(m_axil_wvalid),
      .s_axil_wdata (m_axil_wdata),
      .s_axil_wstrb (m_axil_wstrb),
      .s_axil_wready(m_axil_wready),

      .s_axil_bvalid(m_axil_bvalid),
      .s_axil_bresp (m_axil_bresp),
      .s_axil_bready(m_axil_bready),

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_arready(m_axil_arready),

      .s_axil_rvalid(m_axil_rvalid),
      .s_axil_rdata (m_axil_rdata),
      .s_axil_rresp (m_axil_rresp),
      .s_axil_rready(m_axil_rready),

      .m_axil_awvalid(s_axil_awvalid),
      .m_axil_awaddr (s_axil_awaddr),
      .m_axil_awready(s_axil_awready),

      .m_axil_wvalid(s_axil_wvalid),
      .m_axil_wdata (s_axil_wdata),
      .m_axil_wstrb (s_axil_wstrb),
      .m_axil_wready(s_axil_wready),

      .m_axil_bvalid(s_axil_bvalid),
      .m_axil_bresp (s_axil_bresp),
      .m_axil_bready(s_axil_bready),

      .m_axil_arvalid(s_axil_arvalid),
      .m_axil_araddr (s_axil_araddr),
      .m_axil_arready(s_axil_arready),

      .m_axil_rvalid(s_axil_rvalid),
      .m_axil_rdata (s_axil_rdata),
      .m_axil_rresp (s_axil_rresp),
      .m_axil_rready(s_axil_rready)
  );

  // Initialize signals in reset
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_awvalid <= 1'b0;
      m_axil_awaddr  <= '0;
      m_axil_wvalid  <= 1'b0;
      m_axil_wdata   <= '0;
      m_axil_wstrb   <= '0;
      m_axil_bready  <= 1'b0;
      m_axil_arvalid <= 1'b0;
      m_axil_araddr  <= '0;
      m_axil_rready  <= 1'b0;

      for (int i = 0; i < NUM_S; i++) begin
        s_axil_awready[i] <= 1'b0;
        s_axil_wready[i]  <= 1'b0;
        s_axil_bvalid[i]  <= 1'b0;
        s_axil_bresp[i]   <= 2'b00;
        s_axil_arready[i] <= 1'b0;
        s_axil_rvalid[i]  <= 1'b0;
        s_axil_rdata[i]   <= '0;
        s_axil_rresp[i]   <= 2'b00;
      end
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(m_axil_rvalid);
    `CHECK_FALSE(m_axil_bvalid);

    for (int i = 0; i < NUM_S; i++) begin
      `CHECK_FALSE(s_axil_awvalid[i]);
      `CHECK_FALSE(s_axil_wvalid[i]);
      `CHECK_FALSE(s_axil_arvalid[i]);
    end

    `CHECK_FALSE(uut.svc_axil_router_rd_i.active);
    `CHECK_FALSE(uut.svc_axil_router_wr_i.active);
    `CHECK_FALSE(uut.svc_axil_router_rd_i.bus_err);
    `CHECK_FALSE(uut.svc_axil_router_wr_i.bus_err);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_router_tb);
  `TEST_CASE(test_reset);
  `TEST_SUITE_END();

endmodule
