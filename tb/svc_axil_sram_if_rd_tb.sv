`include "svc_tb_unit.sv"

`include "svc_axil_sram_if_rd.sv"

// verilator lint_off: UNUSEDSIGNAL
module svc_axil_sram_if_rd_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic           m_axil_arvalid;
  logic           m_axil_arready;
  logic [ AW-1:0] m_axil_araddr;
  logic [ DW-1:0] m_axil_rdata;
  logic [    1:0] m_axil_rresp;
  logic           m_axil_rvalid;
  logic           m_axil_rready;

  logic           sram_rd_cmd_valid;
  logic           sram_rd_cmd_ready;
  logic [SAW-1:0] sram_rd_cmd_addr;
  logic           sram_rd_resp_valid;
  logic           sram_rd_resp_ready;
  logic [ DW-1:0] sram_rd_resp_data;

  svc_axil_sram_if_rd #(
      .AXIL_ADDR_WIDTH(AW),
      .AXIL_DATA_WIDTH(DW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_arready(m_axil_arready),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_rdata  (m_axil_rdata),
      .s_axil_rresp  (m_axil_rresp),
      .s_axil_rvalid (m_axil_rvalid),
      .s_axil_rready (m_axil_rready),

      .sram_rd_cmd_valid (sram_rd_cmd_valid),
      .sram_rd_cmd_ready (sram_rd_cmd_ready),
      .sram_rd_cmd_addr  (sram_rd_cmd_addr),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_arvalid     <= 1'b0;
      m_axil_araddr      <= '0;
      m_axil_rready      <= 1'b0;

      sram_rd_cmd_ready  <= 1'b0;
      sram_rd_resp_valid <= 1'b0;
      sram_rd_resp_data  <= '0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axil_arvalid && m_axil_arready) begin
      m_axil_arvalid <= 1'b0;
    end
  end

  task test_initial;
    `ASSERT_EQ(sram_rd_cmd_valid, 1'b0);
    `ASSERT_EQ(m_axil_rvalid, 1'b0);
  endtask

  task automatic test_ar_sram_ready;
    logic [AW-1:0] addr = AW'(16'hA000);

    `ASSERT_EQ(sram_rd_cmd_valid, 1'b0);
    m_axil_arvalid = 1'b1;
    m_axil_araddr  = addr;

    repeat (3) begin
      @(posedge clk);
      `ASSERT_EQ(sram_rd_cmd_valid, 1'b1);
      `ASSERT_EQ(sram_rd_cmd_addr, SAW'(addr[AW-1:LSB]));
    end

    sram_rd_cmd_ready = 1'b1;
    @(posedge clk);
    #1;
    `ASSERT_EQ(sram_rd_cmd_valid, 1'b0);
    `ASSERT_EQ(sram_rd_cmd_addr, SAW'(addr[AW-1:LSB]));
  endtask

  task automatic test_r_axi_rready;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    `ASSERT_EQ(m_axil_rvalid, 1'b0);
    m_axil_arvalid    = 1'b1;
    m_axil_araddr     = addr;
    sram_rd_cmd_ready = 1'b1;

    @(posedge clk);
    #1;
    `ASSERT_EQ(m_axil_rvalid, 1'b0);
    `ASSERT_EQ(sram_rd_resp_ready, 1'b0);

    sram_rd_resp_valid = 1'b1;
    sram_rd_resp_data  = data;
    `ASSERT_EQ(m_axil_rvalid, 1'b1);
    `ASSERT_EQ(m_axil_rdata, data);
    `ASSERT_EQ(sram_rd_resp_ready, 1'b0);

    repeat (3) begin
      @(posedge clk);
      `ASSERT_EQ(m_axil_rvalid, 1'b1);
      `ASSERT_EQ(m_axil_rdata, data);
      `ASSERT_EQ(sram_rd_resp_ready, 1'b0);
    end

    m_axil_rready = 1'b1;
    `ASSERT_EQ(sram_rd_resp_ready, 1'b1);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_sram_if_rd_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_ar_sram_ready);
  `TEST_CASE(test_r_axi_rready);
  `TEST_SUITE_END();

endmodule