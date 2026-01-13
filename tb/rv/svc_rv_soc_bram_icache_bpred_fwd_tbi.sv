`include "svc_unit.sv"

`include "svc_axi_mem.sv"
`include "svc_mem_bram.sv"
`include "svc_rv_soc_bram_cache.sv"

module svc_rv_soc_bram_icache_bpred_fwd_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // AXI parameters - must match SoC
  //
  localparam int AXI_ADDR_WIDTH = 32;
  localparam int AXI_DATA_WIDTH = 128;
  localparam int AXI_ID_WIDTH = 4;

  //
  // CPI expectations with cached data memory, forwarding and branch prediction
  //
  localparam real alu_indep_max_cpi = 1.5;
  localparam real alu_chain_max_cpi = 2.9;
  localparam real br_taken_max_cpi = 3.5;
  localparam real br_not_taken_max_cpi = 3.15;
  localparam real load_use_max_cpi = 8.0;
  localparam real mixed_alu_max_cpi = 2.7;
  localparam real function_calls_max_cpi = 3.15;
  localparam real fib12_max_cpi = 3.0;
  localparam real fib100_max_cpi = 2.5;
  localparam real bubble_max_cpi = 5.0;
  localparam real forward_taken_loop_max_cpi = 3.7;

  logic                        ebreak;

  //
  // MMIO interface signals
  //
  logic                        io_ren;
  logic [                31:0] io_raddr;
  logic [                31:0] io_rdata;
  logic                        io_wen;
  logic [                31:0] io_waddr;
  logic [                31:0] io_wdata;
  logic [                 3:0] io_wstrb;

  //
  // AXI signals for data memory backing store
  //
  logic                        m_axi_arvalid;
  logic [    AXI_ID_WIDTH-1:0] m_axi_arid;
  logic [  AXI_ADDR_WIDTH-1:0] m_axi_araddr;
  logic [                 7:0] m_axi_arlen;
  logic [                 2:0] m_axi_arsize;
  logic [                 1:0] m_axi_arburst;
  logic                        m_axi_arready;

  logic                        m_axi_rvalid;
  logic [    AXI_ID_WIDTH-1:0] m_axi_rid;
  logic [  AXI_DATA_WIDTH-1:0] m_axi_rdata;
  logic [                 1:0] m_axi_rresp;
  logic                        m_axi_rlast;
  logic                        m_axi_rready;

  logic                        m_axi_awvalid;
  logic [    AXI_ID_WIDTH-1:0] m_axi_awid;
  logic [  AXI_ADDR_WIDTH-1:0] m_axi_awaddr;
  logic [                 7:0] m_axi_awlen;
  logic [                 2:0] m_axi_awsize;
  logic [                 1:0] m_axi_awburst;
  logic                        m_axi_awready;

  logic                        m_axi_wvalid;
  logic [  AXI_DATA_WIDTH-1:0] m_axi_wdata;
  logic [AXI_DATA_WIDTH/8-1:0] m_axi_wstrb;
  logic                        m_axi_wlast;
  logic                        m_axi_wready;

  logic                        m_axi_bvalid;
  logic [    AXI_ID_WIDTH-1:0] m_axi_bid;
  logic [                 1:0] m_axi_bresp;
  logic                        m_axi_bready;

  //
  // System under test
  //
  svc_rv_soc_bram_cache #(
      .IMEM_DEPTH   (IMEM_DEPTH),
      .PIPELINED    (1),
      .FWD_REGFILE  (1),
      .ICACHE_ENABLE(1),
      .DCACHE_ENABLE(0),
      .FWD          (1),
      .BPRED        (1),
      .BTB_ENABLE   (0),
      .BTB_ENTRIES  (16),

      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) uut (
      .dbg_urx_valid(1'b0),
      .dbg_urx_data (8'h0),
      .dbg_urx_ready(),
      .dbg_utx_valid(),
      .dbg_utx_data (),
      .dbg_utx_ready(1'b1),

      .clk  (clk),
      .rst_n(rst_n),

      .io_ren  (io_ren),
      .io_raddr(io_raddr),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(io_wstrb),

      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arid   (m_axi_arid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),

      .m_axi_rvalid(m_axi_rvalid),
      .m_axi_rid   (m_axi_rid),
      .m_axi_rdata (m_axi_rdata),
      .m_axi_rresp (m_axi_rresp),
      .m_axi_rlast (m_axi_rlast),
      .m_axi_rready(m_axi_rready),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),

      .m_axi_wvalid(m_axi_wvalid),
      .m_axi_wdata (m_axi_wdata),
      .m_axi_wstrb (m_axi_wstrb),
      .m_axi_wlast (m_axi_wlast),
      .m_axi_wready(m_axi_wready),

      .m_axi_bvalid(m_axi_bvalid),
      .m_axi_bid   (m_axi_bid),
      .m_axi_bresp (m_axi_bresp),
      .m_axi_bready(m_axi_bready),

      .ebreak(ebreak),
      .trap  ()
  );

  //
  // AXI memory backing store for data cache
  //
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(16),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) axi_dmem (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr[15:0]),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),

      .s_axi_rvalid(m_axi_rvalid),
      .s_axi_rid   (m_axi_rid),
      .s_axi_rdata (m_axi_rdata),
      .s_axi_rresp (m_axi_rresp),
      .s_axi_rlast (m_axi_rlast),
      .s_axi_rready(m_axi_rready),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr[15:0]),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awready(m_axi_awready),

      .s_axi_wvalid(m_axi_wvalid),
      .s_axi_wdata (m_axi_wdata),
      .s_axi_wstrb (m_axi_wstrb),
      .s_axi_wlast (m_axi_wlast),
      .s_axi_wready(m_axi_wready),

      .s_axi_bvalid(m_axi_bvalid),
      .s_axi_bid   (m_axi_bid),
      .s_axi_bresp (m_axi_bresp),
      .s_axi_bready(m_axi_bready)
  );

  //
  // Memory-mapped I/O memory
  //
  svc_mem_bram #(
      .DW   (32),
      .DEPTH(2 ** IO_AW)
  ) io_mem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_en  (io_ren),
      .rd_addr(io_raddr),
      .rd_data(io_rdata),

      .wr_en  (io_wen),
      .wr_addr(io_waddr),
      .wr_data(io_wdata),
      .wr_strb(io_wstrb)
  );

  //
  // Override imem backdoor macro for AXI memory
  //
  `define IMEM_WR(i, val) axi_dmem.mem[(i) >> 2][((i) & 3) * 32 +: 32] = val
  `define IMEM_RD(i) axi_dmem.mem[(i) >> 2][((i) & 3) * 32 +: 32]

  //
  // Upper address bits unused (memory is 64KB)
  //
  `SVC_UNUSED({m_axi_araddr[31:16], m_axi_awaddr[31:16]})

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_icache_bpred_fwd_tbi, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
