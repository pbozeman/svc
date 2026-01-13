`include "svc_unit.sv"

`include "svc_ice40_axil_sram.sv"
`include "svc_model_sram.sv"

module svc_ice40_axil_sram_tbi;
  parameter AW = 16;
  parameter DW = 8;
  parameter SW = (DW / 8);
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;

  logic [ AW-1:0] m_axil_awaddr;
  logic           m_axil_awvalid;
  logic           m_axil_awready;
  logic [ DW-1:0] m_axil_wdata;
  logic [ SW-1:0] m_axil_wstrb;
  logic           m_axil_wvalid;
  logic           m_axil_wready;
  logic [    1:0] m_axil_bresp;
  logic           m_axil_bvalid;
  logic           m_axil_bready;

  logic           m_axil_arvalid;
  logic [ AW-1:0] m_axil_araddr;
  logic           m_axil_arready;
  logic [ DW-1:0] m_axil_rdata;
  logic [    1:0] m_axil_rresp;
  logic           m_axil_rvalid;
  logic           m_axil_rready;

  logic [SAW-1:0] sram_io_addr;
  wire  [ DW-1:0] sram_io_data;
  logic           sram_io_we_n;
  logic           sram_io_oe_n;
  logic           sram_io_ce_n;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  svc_ice40_axil_sram #(
      .AXIL_ADDR_WIDTH(AW),
      .AXIL_DATA_WIDTH(DW)
  ) svc_ice40_axil_sram_i (
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

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_arready(m_axil_arready),
      .s_axil_rdata  (m_axil_rdata),
      .s_axil_rresp  (m_axil_rresp),
      .s_axil_rvalid (m_axil_rvalid),
      .s_axil_rready (m_axil_rready),

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
      m_axil_awaddr  <= '0;
      m_axil_awvalid <= 1'b0;
      m_axil_wdata   <= '0;
      m_axil_wstrb   <= '0;
      m_axil_wvalid  <= 1'b0;
      m_axil_bready  <= 1'b0;
      m_axil_arvalid <= 1'b0;
      m_axil_araddr  <= '0;
      m_axil_rready  <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axil_awvalid && m_axil_awready) begin
      m_axil_awvalid <= 1'b0;
    end

    if (m_axil_wvalid && m_axil_wready) begin
      m_axil_wvalid <= 1'b0;
    end

    if (m_axil_arvalid && m_axil_arready) begin
      m_axil_arvalid <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(m_axil_bvalid);
    `CHECK_FALSE(m_axil_rvalid);
  endtask

  // Basic smoke test
  task automatic test_io;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);
      logic [DW-1:0] data = DW'(16'hD000);

      // write
      m_axil_awvalid = 1'b1;
      m_axil_awaddr  = addr;

      m_axil_wvalid  = 1'b1;
      m_axil_wdata   = data;
      m_axil_wstrb   = '1;

      m_axil_bready  = 1'b1;

      `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
      `CHECK_EQ(m_axil_bresp, 2'b00);
      `TICK(clk);
      `CHECK_FALSE(m_axil_bvalid);

      // read it back
      m_axil_arvalid = 1'b1;
      m_axil_araddr  = addr;

      m_axil_rready  = 1'b1;
      `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
      `CHECK_EQ(m_axil_rdata, data);
      `CHECK_EQ(m_axil_rresp, 2'b00);

      `TICK(clk);
      `CHECK_FALSE(m_axil_rvalid);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_ice40_axil_sram_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_io);
  `TEST_SUITE_END();

endmodule
