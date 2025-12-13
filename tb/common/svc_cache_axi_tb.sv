`include "svc_unit.sv"

`include "svc_cache_axi.sv"
`include "svc_axi_mem.sv"

module svc_cache_axi_tb;
  //
  // Mirror of svc_cache_axi state enum for testbench access
  //
  typedef enum {
    STATE_IDLE,
    STATE_READ_BURST
  } state_t;

  localparam CACHE_SIZE_BYTES = 256;
  localparam CACHE_ADDR_WIDTH = 32;
  localparam CACHE_LINE_BYTES = 16;
  localparam AXI_ADDR_WIDTH = 12;
  localparam AXI_DATA_WIDTH = 32;
  localparam AXI_ID_WIDTH = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // CPU interface
  //
  logic                      ren;
  logic                      wen;
  logic [              31:0] addr;
  logic [              31:0] rd_data;
  logic                      rd_valid;
  logic [              31:0] wr_data;
  logic [               3:0] wr_strb;

  //
  // AXI interface
  //
  logic                      axi_arvalid;
  logic [  AXI_ID_WIDTH-1:0] axi_arid;
  logic [AXI_ADDR_WIDTH-1:0] axi_araddr;
  logic [               7:0] axi_arlen;
  logic [               2:0] axi_arsize;
  logic [               1:0] axi_arburst;
  logic                      axi_arready;

  logic                      axi_rvalid;
  logic [  AXI_ID_WIDTH-1:0] axi_rid;
  logic [AXI_DATA_WIDTH-1:0] axi_rdata;
  logic [               1:0] axi_rresp;
  logic                      axi_rlast;
  logic                      axi_rready;

  logic                      axi_awvalid;
  logic [  AXI_ID_WIDTH-1:0] axi_awid;
  logic [AXI_ADDR_WIDTH-1:0] axi_awaddr;
  logic [               7:0] axi_awlen;
  logic [               2:0] axi_awsize;
  logic [               1:0] axi_awburst;
  logic                      axi_awready;

  logic                      axi_wvalid;
  logic [AXI_DATA_WIDTH-1:0] axi_wdata;
  logic [               3:0] axi_wstrb;
  logic                      axi_wlast;
  logic                      axi_wready;

  logic                      axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] axi_bid;
  logic [               1:0] axi_bresp;
  logic                      axi_bready;

  //
  // Cache under test
  //
  svc_cache_axi #(
      .CACHE_SIZE_BYTES(CACHE_SIZE_BYTES),
      .CACHE_ADDR_WIDTH(CACHE_ADDR_WIDTH),
      .CACHE_LINE_BYTES(CACHE_LINE_BYTES),
      .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH    (AXI_ID_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .ren     (ren),
      .wen     (wen),
      .addr    (addr),
      .rd_data (rd_data),
      .rd_valid(rd_valid),
      .wr_data (wr_data),
      .wr_strb (wr_strb),

      .m_axi_arvalid(axi_arvalid),
      .m_axi_arid   (axi_arid),
      .m_axi_araddr (axi_araddr),
      .m_axi_arlen  (axi_arlen),
      .m_axi_arsize (axi_arsize),
      .m_axi_arburst(axi_arburst),
      .m_axi_arready(axi_arready),

      .m_axi_rvalid(axi_rvalid),
      .m_axi_rid   (axi_rid),
      .m_axi_rdata (axi_rdata),
      .m_axi_rresp (axi_rresp),
      .m_axi_rlast (axi_rlast),
      .m_axi_rready(axi_rready),

      .m_axi_awvalid(axi_awvalid),
      .m_axi_awid   (axi_awid),
      .m_axi_awaddr (axi_awaddr),
      .m_axi_awlen  (axi_awlen),
      .m_axi_awsize (axi_awsize),
      .m_axi_awburst(axi_awburst),
      .m_axi_awready(axi_awready),

      .m_axi_wvalid(axi_wvalid),
      .m_axi_wdata (axi_wdata),
      .m_axi_wstrb (axi_wstrb),
      .m_axi_wlast (axi_wlast),
      .m_axi_wready(axi_wready),

      .m_axi_bvalid(axi_bvalid),
      .m_axi_bid   (axi_bid),
      .m_axi_bresp (axi_bresp),
      .m_axi_bready(axi_bready)
  );

  //
  // AXI memory backing store
  //
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) axi_mem (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(axi_arvalid),
      .s_axi_arid   (axi_arid),
      .s_axi_araddr (axi_araddr),
      .s_axi_arlen  (axi_arlen),
      .s_axi_arsize (axi_arsize),
      .s_axi_arburst(axi_arburst),
      .s_axi_arready(axi_arready),

      .s_axi_rvalid(axi_rvalid),
      .s_axi_rid   (axi_rid),
      .s_axi_rdata (axi_rdata),
      .s_axi_rresp (axi_rresp),
      .s_axi_rlast (axi_rlast),
      .s_axi_rready(axi_rready),

      .s_axi_awvalid(axi_awvalid),
      .s_axi_awid   (axi_awid),
      .s_axi_awaddr (axi_awaddr),
      .s_axi_awlen  (axi_awlen),
      .s_axi_awsize (axi_awsize),
      .s_axi_awburst(axi_awburst),
      .s_axi_awready(axi_awready),

      .s_axi_wvalid(axi_wvalid),
      .s_axi_wdata (axi_wdata),
      .s_axi_wstrb (axi_wstrb),
      .s_axi_wlast (axi_wlast),
      .s_axi_wready(axi_wready),

      .s_axi_bvalid(axi_bvalid),
      .s_axi_bid   (axi_bid),
      .s_axi_bresp (axi_bresp),
      .s_axi_bready(axi_bready)
  );

  //
  // Test: Reset state
  //
  task automatic test_reset;
    `CHECK_FALSE(rd_valid);
    `CHECK_EQ(rd_data, '0);
    `CHECK_FALSE(axi_arvalid);
    `CHECK_FALSE(axi_awvalid);
    `CHECK_FALSE(axi_wvalid);
  endtask

  //
  // Test: Read miss transitions to STATE_READ_BURST
  //
  task automatic test_read_miss;
    addr = 32'h100;
    ren  = 1;

    `TICK(clk);
    `CHECK_EQ(uut.state, STATE_READ_BURST);
  endtask

  //
  // Reset and memory initialization
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      ren                   <= 0;
      wen                   <= 0;
      addr                  <= 0;
      wr_data               <= 0;
      wr_strb               <= 0;

      axi_mem.mem['h200>>2] <= 32'hDEADBEEF;
      axi_mem.mem['h300>>2] <= 32'hCAC4ED00;
    end
  end

  //
  // Test: Read miss fetches data correctly
  //
  task automatic test_read_miss_data;
    addr = 32'h200;
    ren  = 1;

    `CHECK_WAIT_FOR(clk, rd_valid, 8);
    `CHECK_EQ(rd_data, 32'hDEADBEEF);
  endtask

  //
  // Test: Cache hit returns data immediately
  //
  task automatic test_cache_hit;
    // First read - cache miss
    addr = 32'h300;
    ren  = 1;
    `TICK(clk);
    ren = 0;

    `CHECK_WAIT_FOR(clk, rd_valid, 8);
    `CHECK_EQ(rd_data, 32'hCAC4ED00);

    // Second read - should hit cache
    ren = 1;
    `TICK(clk);
    `CHECK_TRUE(rd_valid);
    `CHECK_EQ(rd_data, 32'hCAC4ED00);
  endtask


  `TEST_SUITE_BEGIN(svc_cache_axi_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_read_miss);
  `TEST_CASE(test_read_miss_data);
  `TEST_CASE(test_cache_hit);
  `TEST_SUITE_END();

endmodule
