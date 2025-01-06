`include "svc_unit.sv"

`include "svc_axi_ice40_sram.sv"
`include "svc_model_sram.sv"

// verilator lint_off: UNUSEDSIGNAL
// verilator lint_off: UNDRIVEN
module svc_axi_ice40_sram_tb;
  parameter AW = 16;
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

  logic [  SAW-1:0] sram_io_addr;
  wire  [   DW-1:0] sram_io_data;
  logic             sram_io_we_n;
  logic             sram_io_oe_n;
  logic             sram_io_ce_n;

  svc_axi_ice40_sram #(
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

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

  svc_model_sram #(
      .ADDR_WIDTH(SAW),
      .DATA_WIDTH(DW)
  ) svc_model_sram_i (
      .rst_n  (rst_n),
      .we_n   (sram_io_we_n),
      .oe_n   (sram_io_oe_n),
      .ce_n   (sram_io_ce_n),
      .addr   (sram_io_addr),
      .data_io(sram_io_data)
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
    end
  end

  task test_initial;
    `CHECK_FALSE(m_axi_bvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_ice40_sram_tb);

  `TEST_CASE(test_initial);

  `TEST_SUITE_END();

endmodule
