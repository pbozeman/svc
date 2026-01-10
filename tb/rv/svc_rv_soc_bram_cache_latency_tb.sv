`include "svc_unit.sv"

`include "svc_axi_mem_latency.sv"
`include "svc_mem_bram.sv"
`include "svc_rv_soc_bram_cache.sv"

//
// Cache testbench with AXI latency injection.
//
// Tests cache behavior under DDR3-like latency to catch timing-sensitive bugs.
// Uses plusargs for runtime latency configuration:
//   +READ_LATENCY=<cycles>   (default: 30)
//   +WRITE_LATENCY=<cycles>  (default: 10)
//
module svc_rv_soc_bram_cache_latency_tb;
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
  // CPI expectations with latency injection
  //
  // Higher latency means more cache miss penalty, so CPI bounds are relaxed.
  //
  localparam real alu_indep_max_cpi = 3.0;
  localparam real alu_chain_max_cpi = 5.0;
  localparam real br_taken_max_cpi = 6.0;
  localparam real br_not_taken_max_cpi = 5.0;
  localparam real load_use_max_cpi = 15.0;
  localparam real mixed_alu_max_cpi = 5.0;
  localparam real function_calls_max_cpi = 6.0;
  localparam real fib12_max_cpi = 6.0;
  localparam real fib100_max_cpi = 5.0;
  localparam real bubble_max_cpi = 10.0;
  localparam real forward_taken_loop_max_cpi = 7.0;

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
  // AXI signals for memory backing store
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
      .DCACHE_ENABLE(1),

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
  // AXI memory backing store with latency injection
  //
  // Default latency approximates DDR3/MIG timing (~30 cycles read, ~10 write)
  //
  svc_axi_mem_latency #(
      .AXI_ADDR_WIDTH    (16),
      .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH      (AXI_ID_WIDTH),
      .AW_ACCEPT_LATENCY (10),
      .W_ACCEPT_LATENCY  (10),
      .READ_RESP_LATENCY (50),
      .WRITE_RESP_LATENCY(20),
      .RANDOM_LATENCY    (1)
  ) axi_mem (
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
  // Override imem and dmem backdoor macros for AXI memory
  //
  // Access the underlying svc_axi_mem inside the latency wrapper
  //
  localparam int DMEM_WORD_OFFSET = 'h1000 / 4;

  `define IMEM_WR(
      i, val) axi_mem.axi_mem_inst.mem[(i) >> 2][((i) & 3) * 32 +: 32] = val
  `define IMEM_RD(i) axi_mem.axi_mem_inst.mem[(i) >> 2][((i) & 3) * 32 +: 32]
  `define DMEM_RD(
      i) axi_mem.axi_mem_inst.mem[(DMEM_WORD_OFFSET + (i)) >> 2][((DMEM_WORD_OFFSET + (i)) & 3) * 32 +: 32]
  `define DMEM_WR(i,
                  val) axi_mem.axi_mem_inst.mem[(DMEM_WORD_OFFSET + (i)) >> 2][((DMEM_WORD_OFFSET + (i)) & 3) * 32 +: 32] = val

  //
  // Upper address bits unused (memory is 64KB)
  //
  `SVC_UNUSED({m_axi_araddr[31:16], m_axi_awaddr[31:16]})

  //
  // Flush cycles after EBREAK to allow writes to complete through latency
  //
  `define POST_EBREAK_FLUSH_CYCLES 100

  //
  // Increase default timeout for random latency
  //
  `define CHECK_WAIT_FOR_EBREAK_TIMEOUT 2048

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  // Extended timeout to account for latency overhead
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_cache_latency_tb, 500000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
