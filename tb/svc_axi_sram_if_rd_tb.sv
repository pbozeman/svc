`include "svc_unit.sv"

`include "svc_axi_sram_if_rd.sv"

// verilator lint_off: UNUSEDSIGNAL
// verilator lint_off: UNDRIVEN
module svc_axi_sram_if_rd_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IW = 4;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic           m_axi_arvalid;
  logic           m_axi_arready;
  logic [ IW-1:0] m_axi_arid;
  logic [ AW-1:0] m_axi_araddr;
  logic [    7:0] m_axi_arlen;
  logic [    2:0] m_axi_arsize;
  logic [    1:0] m_axi_arburst;
  logic           m_axi_rvalid;
  logic           m_axi_rready;
  logic [ IW-1:0] m_axi_rid;
  logic [ DW-1:0] m_axi_rdata;
  logic [    1:0] m_axi_rresp;
  logic           m_axi_rlast;

  logic           sram_rd_cmd_valid;
  logic           sram_rd_cmd_ready;
  logic [ IW-1:0] sram_rd_cmd_id;
  logic [SAW-1:0] sram_rd_cmd_addr;
  logic           sram_rd_resp_valid;
  logic           sram_rd_resp_ready;
  logic [ IW-1:0] sram_rd_resp_id;
  logic [ DW-1:0] sram_rd_resp_data;

  svc_axi_sram_if_rd #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

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

      .sram_rd_cmd_valid (sram_rd_cmd_valid),
      .sram_rd_cmd_ready (sram_rd_cmd_ready),
      .sram_rd_cmd_id    (sram_rd_cmd_id),
      .sram_rd_cmd_addr  (sram_rd_cmd_addr),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_id   (sram_rd_resp_id),
      .sram_rd_resp_data (sram_rd_resp_data)
  );


  `TEST_SUITE_BEGIN(svc_axi_sram_if_rd_tb);
  // TODO
  `TEST_SUITE_END();

endmodule
