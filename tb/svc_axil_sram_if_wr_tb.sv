`include "svc_unit.sv"

`include "svc_axil_sram_if_wr.sv"

// The bulk of the unit testing in in the combined _if_tb module.

module svc_axil_sram_if_wr_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;
  parameter STRBW = (DW / 8);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [   AW-1:0] m_axil_awaddr;
  logic             m_axil_awvalid;
  logic             m_axil_awready;
  logic [   DW-1:0] m_axil_wdata;
  logic [STRBW-1:0] m_axil_wstrb;
  logic             m_axil_wvalid;
  logic             m_axil_wready;
  logic [      1:0] m_axil_bresp;
  logic             m_axil_bvalid;
  logic             m_axil_bready;

  logic             sram_wr_cmd_valid;
  logic             sram_wr_cmd_ready;
  logic [  SAW-1:0] sram_wr_cmd_addr;
  logic [   DW-1:0] sram_wr_cmd_data;
  logic [STRBW-1:0] sram_wr_cmd_strb;

  svc_axil_sram_if_wr #(
      .AXIL_ADDR_WIDTH(AW),
      .AXIL_DATA_WIDTH(DW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awaddr (m_axil_awaddr),
      .s_axil_awvalid(m_axil_awvalid),
      .s_axil_awready(m_axil_awready),
      .s_axil_wdata  (m_axil_wdata),
      .s_axil_wstrb  (m_axil_wstrb),
      .s_axil_wvalid (m_axil_wvalid),
      .s_axil_wready (m_axil_wready),
      .s_axil_bresp  (m_axil_bresp),
      .s_axil_bvalid (m_axil_bvalid),
      .s_axil_bready (m_axil_bready),

      .sram_wr_cmd_valid(sram_wr_cmd_valid),
      .sram_wr_cmd_ready(sram_wr_cmd_ready),
      .sram_wr_cmd_addr (sram_wr_cmd_addr),
      .sram_wr_cmd_data (sram_wr_cmd_data),
      .sram_wr_cmd_strb (sram_wr_cmd_strb)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_awaddr     <= '0;
      m_axil_awvalid    <= 1'b0;
      m_axil_wdata      <= '0;
      m_axil_wstrb      <= '0;
      m_axil_wvalid     <= 1'b0;
      m_axil_bready     <= 1'b0;

      sram_wr_cmd_ready <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axil_awvalid && m_axil_awready) begin
      m_axil_awvalid <= 1'b0;
    end

    if (m_axil_wvalid && m_axil_wready) begin
      m_axil_wvalid <= 1'b0;
    end
  end

  task test_initial;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axil_bvalid, 1'b0);
    `CHECK_EQ(m_axil_bresp, '0);
  endtask

  task automatic test_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);

    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = addr;
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = data;
    m_axil_wstrb   = '1;
    m_axil_bready  = 1'b1;

    repeat (3) begin
      @(posedge clk);
      `CHECK_EQ(sram_wr_cmd_valid, 1'b1);
      `CHECK_EQ(sram_wr_cmd_addr, SAW'(addr[AW-1:LSB]));
      `CHECK_EQ(sram_wr_cmd_data, data);
      `CHECK_EQ(sram_wr_cmd_strb, '1);
      `CHECK_EQ(m_axil_bvalid, 1'b0);
    end

    sram_wr_cmd_ready = 1'b1;
    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axil_bvalid, 1'b1);

    @(posedge clk);
    #1;
    `CHECK_EQ(sram_wr_cmd_valid, 1'b0);
    `CHECK_EQ(m_axil_bvalid, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_sram_if_wr_tb);

  `TEST_CASE(test_initial);
  `TEST_CASE(test_sram_ready);

  `TEST_SUITE_END();

endmodule
