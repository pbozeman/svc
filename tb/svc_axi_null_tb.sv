`include "svc_unit.sv"

`include "svc_axi_null.sv"

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_null_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic            s_axi_awvalid;
  logic [ IDW-1:0] s_axi_awid;
  logic [  AW-1:0] s_axi_awaddr;
  logic [     7:0] s_axi_awlen;
  logic [     2:0] s_axi_awsize;
  logic [     1:0] s_axi_awburst;
  logic            s_axi_awready;

  logic            s_axi_wvalid;
  logic [  DW-1:0] s_axi_wdata;
  logic [DW/8-1:0] s_axi_wstrb;
  logic            s_axi_wlast;
  logic            s_axi_wready;

  logic            s_axi_bvalid;
  logic [ IDW-1:0] s_axi_bid;
  logic [     1:0] s_axi_bresp;
  logic            s_axi_bready;

  logic            s_axi_arvalid;
  logic [ IDW-1:0] s_axi_arid;
  logic [  AW-1:0] s_axi_araddr;
  logic [     7:0] s_axi_arlen;
  logic [     2:0] s_axi_arsize;
  logic [     1:0] s_axi_arburst;
  logic            s_axi_arready;

  logic            s_axi_rvalid;
  logic [ IDW-1:0] s_axi_rid;
  logic [  DW-1:0] s_axi_rdata;
  logic [     1:0] s_axi_rresp;
  logic            s_axi_rlast;
  logic            s_axi_rready;

  svc_axi_null #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

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

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      s_axi_awready <= 1'b1;
      s_axi_wready  <= 1'b1;
      s_axi_arready <= 1'b1;

      s_axi_rvalid  <= 1'b0;
      s_axi_rid     <= 0;
      s_axi_rdata   <= 0;
      s_axi_rresp   <= 0;
      s_axi_rlast   <= 1'b0;

      s_axi_bvalid  <= 1'b0;
      s_axi_bid     <= 0;
      s_axi_bresp   <= 0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
    `CHECK_FALSE(s_axi_rvalid);
    `CHECK_FALSE(s_axi_bvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_null_tb);
  `TEST_CASE(test_initial);
  `TEST_SUITE_END();

endmodule
