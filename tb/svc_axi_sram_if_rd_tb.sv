`include "svc_unit.sv"

`include "svc_axi_sram_if_rd.sv"

// The bulk of the testing of the rd module is in the combined if module as
// the test methods were being duplicated in both places.

module svc_axi_sram_if_rd_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IW = 4;
  parameter MW = IW;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // verilator lint_off: UNUSEDSIGNAL
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
  logic [SAW-1:0] sram_rd_cmd_addr;
  logic [ MW-1:0] sram_rd_cmd_meta;
  logic           sram_rd_cmd_last;
  logic           sram_rd_resp_valid;
  logic           sram_rd_resp_ready;
  logic [ DW-1:0] sram_rd_resp_data;
  // verilator lint_on: UNUSEDSIGNAL

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
      .sram_rd_cmd_addr  (sram_rd_cmd_addr),
      .sram_rd_cmd_meta  (sram_rd_cmd_meta),
      .sram_rd_cmd_last  (sram_rd_cmd_last),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data),
      .sram_rd_resp_meta (),
      .sram_rd_resp_last ()
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_arvalid      <= 1'b0;
      m_axi_arid         <= '0;
      m_axi_araddr       <= '0;
      m_axi_arlen        <= '0;
      m_axi_arsize       <= '0;
      m_axi_arburst      <= '0;

      m_axi_rready       <= 1'b0;

      sram_rd_cmd_ready  <= 1'b0;
      sram_rd_resp_valid <= 1'b0;
      sram_rd_resp_data  <= '0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_arvalid <= 1'b0;
    end
  end

  task test_initial;
    `CHECK_EQ(sram_rd_cmd_valid, 1'b0);
    `CHECK_EQ(m_axi_rvalid, 1'b0);
  endtask

  task automatic test_ar_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);

    `CHECK_EQ(sram_rd_cmd_valid, 1'b0);
    m_axi_arvalid = 1'b1;
    m_axi_arid    = 4'hB;
    m_axi_araddr  = addr;

    repeat (3) begin
      @(posedge clk);
      #1;
      `CHECK_TRUE(sram_rd_cmd_valid);
      `CHECK_EQ(sram_rd_cmd_meta, 4'hB);
      `CHECK_TRUE(sram_rd_cmd_last);
      `CHECK_EQ(sram_rd_cmd_addr, SAW'(addr[AW-1:LSB]));
    end

    sram_rd_cmd_ready = 1'b1;
    @(posedge clk);
    #1;
    `CHECK_EQ(sram_rd_cmd_valid, 1'b0);
  endtask


  `TEST_SUITE_BEGIN(svc_axi_sram_if_rd_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_ar_sram_ready);
  `TEST_SUITE_END();

endmodule
