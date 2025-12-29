`ifndef SVC_RV_SOC_BRAM_CACHE_SV
`define SVC_RV_SOC_BRAM_CACHE_SV

`include "svc.sv"

`include "svc_axi_arbiter.sv"
`include "svc_axi_null.sv"
`include "svc_cache_axi.sv"
`include "svc_mem_bram.sv"
`include "svc_rv.sv"
`include "svc_rv_dmem_cache_if.sv"

//
// RISC-V SoC with BRAM instruction memory and cached data memory
//
// Instruction memory: BRAM with 1-cycle latency
// Data memory: Cache backed by AXI interface to external memory
//
// Address decode:
// - Bit 31 = 0: Data memory (through cache to AXI)
// - Bit 31 = 1: I/O (direct BRAM timing, bypasses cache)
//
module svc_rv_soc_bram_cache #(
    parameter int XLEN          = 32,
    parameter int IMEM_DEPTH    = 1024,
    parameter int PIPELINED     = 1,
    parameter int ICACHE_ENABLE = 0,
    parameter int DCACHE_ENABLE = 1,
    parameter int FWD_REGFILE   = 1,
    parameter int FWD           = 0,
    parameter int BPRED         = 0,
    parameter int BTB_ENABLE    = 0,
    parameter int BTB_ENTRIES   = 16,
    parameter int RAS_ENABLE    = 0,
    parameter int RAS_DEPTH     = 8,
    parameter int EXT_ZMMUL     = 0,
    parameter int EXT_M         = 0,
    parameter int PC_REG        = 0,

    parameter logic [31:0] RESET_PC = 0,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = "",

    //
    // Cache parameters
    //
    parameter int CACHE_SIZE_BYTES = 4096,
    parameter int CACHE_LINE_BYTES = 32,
    parameter bit CACHE_TWO_WAY    = 0,

    //
    // AXI parameters
    //
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 128,
    parameter int AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // Memory-mapped I/O interface
    //
    output logic        io_ren,
    output logic [31:0] io_raddr,
    input  logic [31:0] io_rdata,

    output logic        io_wen,
    output logic [31:0] io_waddr,
    output logic [31:0] io_wdata,
    output logic [ 3:0] io_wstrb,

    //
    // AXI4 manager interface for external data memory
    //

    // Read address channel
    output logic                      m_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,

    // Read data channel
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready,

    // Write address channel
    output logic                      m_axi_awvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,

    // Write data channel
    output logic                        m_axi_wvalid,
    output logic [  AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                        m_axi_wlast,
    input  logic                        m_axi_wready,

    // Write response channel
    input  logic                    m_axi_bvalid,
    input  logic [AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [             1:0] m_axi_bresp,
    output logic                    m_axi_bready,

`ifdef RISCV_FORMAL
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [31:0] rvfi_rd_wdata,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,
    output logic        rvfi_mem_valid,
    output logic        rvfi_mem_instr,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
`endif

    output logic ebreak,
    output logic trap
);
  localparam int IMEM_AW = $clog2(IMEM_DEPTH);

  //
  // Instruction memory interface signals
  //
  logic        imem_ren;
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;

  //
  // CPU data memory interface signals
  //
  logic        dmem_ren;
  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_wen;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  logic        dmem_stall;

  //
  // Cache interface signals
  //
  logic        cache_rd_valid;
  logic        cache_rd_ready;
  logic [31:0] cache_rd_addr;
  logic [31:0] cache_rd_data;
  logic        cache_rd_data_valid;
  logic        cache_rd_hit;

  logic        cache_wr_valid;
  logic        cache_wr_ready;
  logic [31:0] cache_wr_addr;
  logic [31:0] cache_wr_data;
  logic [ 3:0] cache_wr_strb;

  //
  // Internal AXI signals for arbiter
  //
  // Arbiter port 0: I$ (null for now)
  // Arbiter port 1: D$
  //
  // The arbiter adds $clog2(NUM_M) bits to the ID width for routing.
  // Our external interface uses AXI_ID_WIDTH, so we need AXI_ID_WIDTH-1
  // for the internal ID width to leave room for the routing bit.
  //
  localparam int NUM_ARB_M = 2;
  localparam int ARB_INTERNAL_ID_WIDTH = AXI_ID_WIDTH - 1;

  // D$ AXI signals (to arbiter port 1)
  logic                             dcache_axi_arvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] dcache_axi_arid;
  logic [       AXI_ADDR_WIDTH-1:0] dcache_axi_araddr;
  logic [                      7:0] dcache_axi_arlen;
  logic [                      2:0] dcache_axi_arsize;
  logic [                      1:0] dcache_axi_arburst;
  logic                             dcache_axi_arready;

  logic                             dcache_axi_rvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] dcache_axi_rid;
  logic [       AXI_DATA_WIDTH-1:0] dcache_axi_rdata;
  logic [                      1:0] dcache_axi_rresp;
  logic                             dcache_axi_rlast;
  logic                             dcache_axi_rready;

  logic                             dcache_axi_awvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] dcache_axi_awid;
  logic [       AXI_ADDR_WIDTH-1:0] dcache_axi_awaddr;
  logic [                      7:0] dcache_axi_awlen;
  logic [                      2:0] dcache_axi_awsize;
  logic [                      1:0] dcache_axi_awburst;
  logic                             dcache_axi_awready;

  logic                             dcache_axi_wvalid;
  logic [       AXI_DATA_WIDTH-1:0] dcache_axi_wdata;
  logic [     AXI_DATA_WIDTH/8-1:0] dcache_axi_wstrb;
  logic                             dcache_axi_wlast;
  logic                             dcache_axi_wready;

  logic                             dcache_axi_bvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] dcache_axi_bid;
  logic [                      1:0] dcache_axi_bresp;
  logic                             dcache_axi_bready;

  // I$ AXI signals (null client, to arbiter port 0)
  logic                             icache_axi_arvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] icache_axi_arid;
  logic [       AXI_ADDR_WIDTH-1:0] icache_axi_araddr;
  logic [                      7:0] icache_axi_arlen;
  logic [                      2:0] icache_axi_arsize;
  logic [                      1:0] icache_axi_arburst;
  logic                             icache_axi_arready;

  logic                             icache_axi_rvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] icache_axi_rid;
  logic [       AXI_DATA_WIDTH-1:0] icache_axi_rdata;
  logic [                      1:0] icache_axi_rresp;
  logic                             icache_axi_rlast;
  logic                             icache_axi_rready;

  logic                             icache_axi_awvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] icache_axi_awid;
  logic [       AXI_ADDR_WIDTH-1:0] icache_axi_awaddr;
  logic [                      7:0] icache_axi_awlen;
  logic [                      2:0] icache_axi_awsize;
  logic [                      1:0] icache_axi_awburst;
  logic                             icache_axi_awready;

  logic                             icache_axi_wvalid;
  logic [       AXI_DATA_WIDTH-1:0] icache_axi_wdata;
  logic [     AXI_DATA_WIDTH/8-1:0] icache_axi_wstrb;
  logic                             icache_axi_wlast;
  logic                             icache_axi_wready;

  logic                             icache_axi_bvalid;
  logic [ARB_INTERNAL_ID_WIDTH-1:0] icache_axi_bid;
  logic [                      1:0] icache_axi_bresp;
  logic                             icache_axi_bready;

  `include "svc_rv_defs.svh"

  // Only ICACHE_ENABLE=0 and DCACHE_ENABLE=1 is currently supported
  initial begin
    if (ICACHE_ENABLE != 0) begin
      $error("ICACHE_ENABLE=1 is not yet supported");
    end
    if (DCACHE_ENABLE != 1) begin
      $error("DCACHE_ENABLE=0 is not yet supported");
    end
  end

  //
  // RISC-V core
  //
  // DMEM_AW is set to maximum (30 bits, since bit 31 is for I/O select)
  // since actual memory is external via AXI.
  //
  svc_rv #(
      .XLEN       (XLEN),
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (30),
      .PIPELINED  (PIPELINED),
      .FWD_REGFILE(FWD_REGFILE),
      .FWD        (FWD),
      .MEM_TYPE   (MEM_TYPE_BRAM),
      .BPRED      (BPRED),
      .BTB_ENABLE (BTB_ENABLE),
      .BTB_ENTRIES(BTB_ENTRIES),
      .RAS_ENABLE (RAS_ENABLE),
      .RAS_DEPTH  (RAS_DEPTH),
      .EXT_ZMMUL  (EXT_ZMMUL),
      .EXT_M      (EXT_M),
      .PC_REG     (PC_REG),
      .RESET_PC   (RESET_PC)
  ) cpu (
      .clk  (clk),
      .rst_n(rst_n),

      .imem_ren  (imem_ren),
      .imem_raddr(imem_raddr),
      .imem_rdata(imem_rdata),

      .dmem_ren  (dmem_ren),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_wen),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),

      .dmem_stall(dmem_stall),

`ifdef RISCV_FORMAL
      .rvfi_valid    (rvfi_valid),
      .rvfi_order    (rvfi_order),
      .rvfi_insn     (rvfi_insn),
      .rvfi_pc_rdata (rvfi_pc_rdata),
      .rvfi_pc_wdata (rvfi_pc_wdata),
      .rvfi_rs1_addr (rvfi_rs1_addr),
      .rvfi_rs2_addr (rvfi_rs2_addr),
      .rvfi_rd_addr  (rvfi_rd_addr),
      .rvfi_rs1_rdata(rvfi_rs1_rdata),
      .rvfi_rs2_rdata(rvfi_rs2_rdata),
      .rvfi_rd_wdata (rvfi_rd_wdata),
      .rvfi_trap     (rvfi_trap),
      .rvfi_halt     (rvfi_halt),
      .rvfi_intr     (rvfi_intr),
      .rvfi_mode     (rvfi_mode),
      .rvfi_ixl      (rvfi_ixl),
      .rvfi_mem_valid(rvfi_mem_valid),
      .rvfi_mem_instr(rvfi_mem_instr),
      .rvfi_mem_addr (rvfi_mem_addr),
      .rvfi_mem_rmask(rvfi_mem_rmask),
      .rvfi_mem_wmask(rvfi_mem_wmask),
      .rvfi_mem_rdata(rvfi_mem_rdata),
      .rvfi_mem_wdata(rvfi_mem_wdata),
`endif

      .ebreak(ebreak),
      .trap  (trap)
  );

  //
  // Instruction memory (BRAM)
  //
  svc_mem_bram #(
      .DW         (32),
      .DEPTH      (IMEM_DEPTH),
      .INIT_FILE  (IMEM_INIT),
      .RESET_VALUE(32'h00000013)
  ) imem (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_en  (imem_ren),
      .rd_addr(imem_raddr),
      .rd_data(imem_rdata),
      .wr_addr(32'h0),
      .wr_data(32'h0),
      .wr_strb(4'h0),
      .wr_en  (1'b0)
  );

  //
  // Data memory cache interface bridge
  //
  // Converts CPU dmem signals to cache valid/ready protocol.
  // Handles I/O bypass (bit 31 = 1 bypasses cache).
  //
  svc_rv_dmem_cache_if dmem_cache_if (
      .clk  (clk),
      .rst_n(rst_n),

      .dmem_ren  (dmem_ren),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_wen),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),

      .dmem_stall(dmem_stall),

      .cache_rd_valid     (cache_rd_valid),
      .cache_rd_ready     (cache_rd_ready),
      .cache_rd_addr      (cache_rd_addr),
      .cache_rd_data      (cache_rd_data),
      .cache_rd_data_valid(cache_rd_data_valid),
      .cache_rd_hit       (cache_rd_hit),

      .cache_wr_valid(cache_wr_valid),
      .cache_wr_ready(cache_wr_ready),
      .cache_wr_addr (cache_wr_addr),
      .cache_wr_data (cache_wr_data),
      .cache_wr_strb (cache_wr_strb),

      .io_ren  (io_ren),
      .io_raddr(io_raddr),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(io_wstrb)
  );

  //
  // Data cache
  //
  svc_cache_axi #(
      .CACHE_SIZE_BYTES(CACHE_SIZE_BYTES),
      .CACHE_ADDR_WIDTH(32),
      .CACHE_LINE_BYTES(CACHE_LINE_BYTES),
      .TWO_WAY         (CACHE_TWO_WAY),
      .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH    (ARB_INTERNAL_ID_WIDTH)
  ) dcache (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_valid     (cache_rd_valid),
      .rd_ready     (cache_rd_ready),
      .rd_addr      (cache_rd_addr),
      .rd_data      (cache_rd_data),
      .rd_data_valid(cache_rd_data_valid),
      .rd_hit       (cache_rd_hit),

      .wr_valid(cache_wr_valid),
      .wr_ready(cache_wr_ready),
      .wr_addr (cache_wr_addr),
      .wr_data (cache_wr_data),
      .wr_strb (cache_wr_strb),

      .m_axi_arvalid(dcache_axi_arvalid),
      .m_axi_arid   (dcache_axi_arid),
      .m_axi_araddr (dcache_axi_araddr),
      .m_axi_arlen  (dcache_axi_arlen),
      .m_axi_arsize (dcache_axi_arsize),
      .m_axi_arburst(dcache_axi_arburst),
      .m_axi_arready(dcache_axi_arready),

      .m_axi_rvalid(dcache_axi_rvalid),
      .m_axi_rid   (dcache_axi_rid),
      .m_axi_rdata (dcache_axi_rdata),
      .m_axi_rresp (dcache_axi_rresp),
      .m_axi_rlast (dcache_axi_rlast),
      .m_axi_rready(dcache_axi_rready),

      .m_axi_awvalid(dcache_axi_awvalid),
      .m_axi_awid   (dcache_axi_awid),
      .m_axi_awaddr (dcache_axi_awaddr),
      .m_axi_awlen  (dcache_axi_awlen),
      .m_axi_awsize (dcache_axi_awsize),
      .m_axi_awburst(dcache_axi_awburst),
      .m_axi_awready(dcache_axi_awready),

      .m_axi_wvalid(dcache_axi_wvalid),
      .m_axi_wdata (dcache_axi_wdata),
      .m_axi_wstrb (dcache_axi_wstrb),
      .m_axi_wlast (dcache_axi_wlast),
      .m_axi_wready(dcache_axi_wready),

      .m_axi_bvalid(dcache_axi_bvalid),
      .m_axi_bid   (dcache_axi_bid),
      .m_axi_bresp (dcache_axi_bresp),
      .m_axi_bready(dcache_axi_bready)
  );

  //
  // Null AXI client for I$ slot (arbiter port 0)
  //
  // When ICACHE_ENABLE=0, this provides a quiet client that never
  // initiates transactions.
  //
  svc_axi_null #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (ARB_INTERNAL_ID_WIDTH)
  ) icache_null (
      .clk  (clk),
      .rst_n(rst_n),

      .m_axi_arvalid(icache_axi_arvalid),
      .m_axi_arid   (icache_axi_arid),
      .m_axi_araddr (icache_axi_araddr),
      .m_axi_arlen  (icache_axi_arlen),
      .m_axi_arsize (icache_axi_arsize),
      .m_axi_arburst(icache_axi_arburst),
      .m_axi_arready(icache_axi_arready),

      .m_axi_rvalid(icache_axi_rvalid),
      .m_axi_rid   (icache_axi_rid),
      .m_axi_rdata (icache_axi_rdata),
      .m_axi_rresp (icache_axi_rresp),
      .m_axi_rlast (icache_axi_rlast),
      .m_axi_rready(icache_axi_rready),

      .m_axi_awvalid(icache_axi_awvalid),
      .m_axi_awid   (icache_axi_awid),
      .m_axi_awaddr (icache_axi_awaddr),
      .m_axi_awlen  (icache_axi_awlen),
      .m_axi_awsize (icache_axi_awsize),
      .m_axi_awburst(icache_axi_awburst),
      .m_axi_awready(icache_axi_awready),

      .m_axi_wvalid(icache_axi_wvalid),
      .m_axi_wdata (icache_axi_wdata),
      .m_axi_wstrb (icache_axi_wstrb),
      .m_axi_wlast (icache_axi_wlast),
      .m_axi_wready(icache_axi_wready),

      .m_axi_bvalid(icache_axi_bvalid),
      .m_axi_bid   (icache_axi_bid),
      .m_axi_bresp (icache_axi_bresp),
      .m_axi_bready(icache_axi_bready)
  );

  //
  // AXI Arbiter
  //
  // Port 0: I$ (null client for now)
  // Port 1: D$
  //
  svc_axi_arbiter #(
      .NUM_M         (NUM_ARB_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (ARB_INTERNAL_ID_WIDTH)
  ) axi_arbiter (
      .clk  (clk),
      .rst_n(rst_n),

      // Subordinate interface (from caches)
      // Port 0: I$ (null)
      // Port 1: D$
      .s_axi_awvalid({dcache_axi_awvalid, icache_axi_awvalid}),
      .s_axi_awid   ({dcache_axi_awid, icache_axi_awid}),
      .s_axi_awaddr ({dcache_axi_awaddr, icache_axi_awaddr}),
      .s_axi_awlen  ({dcache_axi_awlen, icache_axi_awlen}),
      .s_axi_awsize ({dcache_axi_awsize, icache_axi_awsize}),
      .s_axi_awburst({dcache_axi_awburst, icache_axi_awburst}),
      .s_axi_awready({dcache_axi_awready, icache_axi_awready}),

      .s_axi_wvalid({dcache_axi_wvalid, icache_axi_wvalid}),
      .s_axi_wdata ({dcache_axi_wdata, icache_axi_wdata}),
      .s_axi_wstrb ({dcache_axi_wstrb, icache_axi_wstrb}),
      .s_axi_wlast ({dcache_axi_wlast, icache_axi_wlast}),
      .s_axi_wready({dcache_axi_wready, icache_axi_wready}),

      .s_axi_bvalid({dcache_axi_bvalid, icache_axi_bvalid}),
      .s_axi_bid   ({dcache_axi_bid, icache_axi_bid}),
      .s_axi_bresp ({dcache_axi_bresp, icache_axi_bresp}),
      .s_axi_bready({dcache_axi_bready, icache_axi_bready}),

      .s_axi_arvalid({dcache_axi_arvalid, icache_axi_arvalid}),
      .s_axi_arid   ({dcache_axi_arid, icache_axi_arid}),
      .s_axi_araddr ({dcache_axi_araddr, icache_axi_araddr}),
      .s_axi_arlen  ({dcache_axi_arlen, icache_axi_arlen}),
      .s_axi_arsize ({dcache_axi_arsize, icache_axi_arsize}),
      .s_axi_arburst({dcache_axi_arburst, icache_axi_arburst}),
      .s_axi_arready({dcache_axi_arready, icache_axi_arready}),

      .s_axi_rvalid({dcache_axi_rvalid, icache_axi_rvalid}),
      .s_axi_rid   ({dcache_axi_rid, icache_axi_rid}),
      .s_axi_rdata ({dcache_axi_rdata, icache_axi_rdata}),
      .s_axi_rresp ({dcache_axi_rresp, icache_axi_rresp}),
      .s_axi_rlast ({dcache_axi_rlast, icache_axi_rlast}),
      .s_axi_rready({dcache_axi_rready, icache_axi_rready}),

      // Manager interface (to external memory)
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
      .m_axi_rready(m_axi_rready)
  );

endmodule

`endif
