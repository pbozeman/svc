`ifndef SVC_RV_SOC_BRAM_CACHE_SV
`define SVC_RV_SOC_BRAM_CACHE_SV

`include "svc.sv"

`include "svc_axi_arbiter.sv"
`include "svc_axi_null.sv"
`include "svc_cache_axi.sv"
`include "svc_mem_bram.sv"
`include "svc_rv.sv"
`include "svc_rv_dbg_bridge.sv"
`include "svc_rv_dmem_cache_if.sv"
`include "svc_rv_imem_cache_if.sv"
`include "svc_sync_fifo_n.sv"

//
// RISC-V SoC with optional instruction and data caching
//
// Instruction memory:
// - ICACHE_ENABLE=0: BRAM with 1-cycle latency
// - ICACHE_ENABLE=1: I$ backed by AXI interface to external memory
//
// Data memory:
// - DCACHE_ENABLE=0: BRAM with 1-cycle latency (bit 31 selects I/O)
// - DCACHE_ENABLE=1: D$ backed by AXI interface to external memory (bit 31 selects I/O)
//
// Address decode (data memory):
// - Bit 31 = 0: Data memory
// - Bit 31 = 1: I/O
//
module svc_rv_soc_bram_cache #(
    parameter int XLEN          = 32,
    parameter int IMEM_DEPTH    = 1024,
    parameter int DMEM_DEPTH    = 1024,
    parameter int PIPELINED     = 1,
    parameter int ICACHE_ENABLE = 1,
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

    parameter int DEBUG_ENABLED = 0,

    parameter logic [31:0] RESET_PC = 0,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = "",
    // verilog_lint: waive explicit-parameter-storage-type
    parameter DMEM_INIT = "",

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
    // Debug UART interface
    //
    input  logic       dbg_urx_valid,
    input  logic [7:0] dbg_urx_data,
    output logic       dbg_urx_ready,

    output logic       dbg_utx_valid,
    output logic [7:0] dbg_utx_data,
    input  logic       dbg_utx_ready,

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

    output logic        formal_imem_ren,
    output logic [31:0] formal_imem_raddr,
    output logic        formal_dmem_ren,
    output logic [31:0] formal_dmem_raddr,
    output logic        formal_dmem_wen,
    output logic [31:0] formal_dmem_waddr,
`endif

    output logic ebreak,
    output logic trap
);
  localparam int IMEM_AW = $clog2(IMEM_DEPTH);
  localparam int DMEM_AW = (DCACHE_ENABLE != 0) ? 30 : $clog2(DMEM_DEPTH);

  //
  // Instruction memory interface signals
  //
  logic               imem_ren;
  logic [       31:0] imem_raddr;
  logic [       31:0] imem_rdata;
  logic               imem_stall;
  logic [       31:0] imem_rdata_bram;

  //
  // CPU data memory interface signals
  //
  logic               dmem_ren;
  logic [       31:0] dmem_raddr;
  logic [       31:0] dmem_rdata;

  logic               dmem_wen;
  logic [       31:0] dmem_waddr;
  logic [       31:0] dmem_wdata;
  logic [        3:0] dmem_wstrb;

  logic               dmem_stall;

  //
  // Debug bridge signals
  //
  logic               dbg_stall;
  logic               dbg_rst_n;
  logic               dbg_imem_wen;
  logic [IMEM_AW-1:0] dbg_imem_waddr;
  logic [       31:0] dbg_imem_wdata;
  logic [        3:0] dbg_imem_wstrb;
  logic               dbg_dmem_wen;
  logic [DMEM_AW-1:0] dbg_dmem_waddr;
  logic [       31:0] dbg_dmem_wdata;
  logic [        3:0] dbg_dmem_wstrb;
  logic               dbg_dmem_busy;

  // CPU control signals (active when debug is enabled)
  logic               cpu_stall;
  logic               cpu_rst_n;

  assign cpu_rst_n = rst_n && dbg_rst_n;
  assign cpu_stall = dbg_stall;

  //
  // Debug bridge (optional)
  //
  // For cache mode, use von Neumann addressing:
  // - DMEM_BASE_ADDR=0: All writes route to D$ path
  // - Both I$ and D$ fetch from same external DRAM
  //
  if (DEBUG_ENABLED != 0) begin : g_dbg
    // Flow control for debug burst writes.
    //
    // When DCACHE_ENABLE=1, debug writes are funneled through svc_rv_dmem_cache_if
    // and svc_cache_axi, which may deassert ready while an AXI write is in-flight.
    // If we don't backpressure the debug bridge, it can drop writes (the cache
    // interface accepts one store at a time).
    assign dbg_dmem_busy = dmem_stall;

    //
    // Debug UART RX buffering
    //
    // svc_uart_rx has minimal buffering and will drop bytes if the consumer
    // deasserts ready across byte boundaries. In cache/AXI configurations, the
    // debug bridge may need to pause between words while stores complete, so add
    // a small FIFO to absorb UART traffic and avoid protocol desynchronization.
    //
    // TODO: eval if this was really needed
    //
    localparam int DBG_URX_FIFO_AW = 10;  // 1024 bytes
    logic       dbg_urx_fifo_w_inc;
    logic       dbg_urx_fifo_w_full_n;
    logic       dbg_urx_fifo_r_inc;
    logic       dbg_urx_fifo_r_empty_n;
    logic [7:0] dbg_urx_fifo_r_data;
    logic       dbg_urx_ready_int;
    logic       dbg_urx_valid_int;
    logic [7:0] dbg_urx_data_int;

    assign dbg_urx_ready      = dbg_urx_fifo_w_full_n;
    assign dbg_urx_fifo_w_inc = dbg_urx_valid && dbg_urx_ready;
    assign dbg_urx_valid_int  = dbg_urx_fifo_r_empty_n;
    assign dbg_urx_data_int   = dbg_urx_fifo_r_data;
    assign dbg_urx_fifo_r_inc = dbg_urx_valid_int && dbg_urx_ready_int;

    svc_sync_fifo_n #(
        .ADDR_WIDTH(DBG_URX_FIFO_AW),
        .DATA_WIDTH(8)
    ) dbg_urx_fifo (
        .clk      (clk),
        .rst_n    (rst_n),
        .clr      (1'b0),
        .w_inc    (dbg_urx_fifo_w_inc),
        .w_data   (dbg_urx_data),
        .w_full_n (dbg_urx_fifo_w_full_n),
        .r_inc    (dbg_urx_fifo_r_inc),
        .r_empty_n(dbg_urx_fifo_r_empty_n),
        .r_data   (dbg_urx_fifo_r_data)
    );

    svc_rv_dbg_bridge #(
        .IMEM_ADDR_WIDTH(IMEM_AW),
        .DMEM_ADDR_WIDTH(DMEM_AW),
        .IMEM_BASE_ADDR (32'hFFFF_FFFF),
        .DMEM_BASE_ADDR (32'h0000_0000)
    ) dbg_bridge (
        .clk  (clk),
        .rst_n(rst_n),

        .urx_valid(dbg_urx_valid_int),
        .urx_data (dbg_urx_data_int),
        .urx_ready(dbg_urx_ready_int),

        .utx_valid(dbg_utx_valid),
        .utx_data (dbg_utx_data),
        .utx_ready(dbg_utx_ready),

        .dbg_stall(dbg_stall),
        .dbg_rst_n(dbg_rst_n),

        .dbg_imem_wen  (dbg_imem_wen),
        .dbg_imem_waddr(dbg_imem_waddr),
        .dbg_imem_wdata(dbg_imem_wdata),
        .dbg_imem_wstrb(dbg_imem_wstrb),

        .dbg_dmem_wen  (dbg_dmem_wen),
        .dbg_dmem_waddr(dbg_dmem_waddr),
        .dbg_dmem_wdata(dbg_dmem_wdata),
        .dbg_dmem_wstrb(dbg_dmem_wstrb),
        .dbg_dmem_busy (dbg_dmem_busy)
    );
  end else begin : g_no_dbg
    assign dbg_stall      = 1'b0;
    assign dbg_rst_n      = 1'b1;
    assign dbg_imem_wen   = 1'b0;
    assign dbg_imem_waddr = '0;
    assign dbg_imem_wdata = '0;
    assign dbg_imem_wstrb = '0;
    assign dbg_dmem_wen   = 1'b0;
    assign dbg_dmem_waddr = '0;
    assign dbg_dmem_wdata = '0;
    assign dbg_dmem_wstrb = '0;
    assign dbg_dmem_busy  = 1'b0;
    assign dbg_urx_ready  = 1'b0;
    assign dbg_utx_valid  = 1'b0;
    assign dbg_utx_data   = 8'h0;

    `SVC_UNUSED({
                dbg_urx_valid,
                dbg_urx_data,
                dbg_utx_ready,
                dbg_imem_wen,
                dbg_imem_waddr,
                dbg_imem_wdata,
                dbg_imem_wstrb,
                dbg_dmem_wen,
                dbg_dmem_waddr,
                dbg_dmem_wdata,
                dbg_dmem_wstrb,
                dbg_dmem_busy
                })
  end

`ifdef RISCV_FORMAL
  assign formal_imem_ren   = imem_ren;
  assign formal_imem_raddr = imem_raddr;
  assign formal_dmem_ren   = dmem_ren;
  assign formal_dmem_raddr = dmem_raddr;
  assign formal_dmem_wen   = dmem_wen;
  assign formal_dmem_waddr = dmem_waddr;
`endif

  // Instruction cache interface
  logic        icache_rd_valid;
  (* max_fanout = 64, keep = "true" *)logic [31:0] icache_rd_addr;
  logic        icache_rd_ready;
  logic [31:0] icache_rd_data;
  logic        icache_rd_data_valid;
  logic        icache_rd_hit;

  logic        icache_wr_ready;

  //
  // Data BRAM interface signals (DCACHE_ENABLE=0)
  //
  logic        bram_ren;
  logic [31:0] bram_rdata;
  logic        bram_wen;

  logic        io_sel_rd;
  logic        io_sel_rd_p1;
  logic        io_sel_wr;

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

  //
  // RISC-V core
  //
  // DMEM_AW is set to maximum (30 bits, since bit 31 is for I/O select)
  // since actual memory may be external via AXI.
  //
  svc_rv #(
      .XLEN       (XLEN),
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
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
      .rst_n(cpu_rst_n),

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

      .dmem_stall(dmem_stall || cpu_stall),
      .imem_stall(imem_stall || cpu_stall),

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
      .rd_data(imem_rdata_bram),
      .wr_addr(32'h0),
      .wr_data(32'h0),
      .wr_strb(4'h0),
      .wr_en  (1'b0)
  );

  //
  // Data memory (BRAM)
  //
  // This is used when DCACHE_ENABLE=0 and provides the default DMEM backdoor
  // path for SoC testbenches via `uut.dmem.mem[...]`.
  //
  svc_mem_bram #(
      .DW       (32),
      .DEPTH    (DMEM_DEPTH),
      .INIT_FILE(DMEM_INIT)
  ) dmem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_en  (bram_ren),
      .rd_addr(dmem_raddr),
      .rd_data(bram_rdata),

      .wr_en  (bram_wen),
      .wr_addr(dmem_waddr),
      .wr_data(dmem_wdata),
      .wr_strb(dmem_wstrb)
  );

  //
  // Instruction memory
  //
  if (ICACHE_ENABLE == 0) begin : g_imem_bram
    assign imem_rdata = imem_rdata_bram;
    assign imem_stall = 1'b0;

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

    // icache signals not used when ICACHE_ENABLE=0
    assign icache_rd_valid      = 1'b0;
    assign icache_rd_addr       = '0;
    assign icache_rd_ready      = 1'b0;
    assign icache_rd_data       = '0;
    assign icache_rd_data_valid = 1'b0;
    assign icache_rd_hit        = 1'b0;
    assign icache_wr_ready      = 1'b0;

    `SVC_UNUSED({
                icache_rd_valid,
                icache_rd_addr,
                icache_rd_ready,
                icache_rd_data,
                icache_rd_data_valid,
                icache_rd_hit,
                icache_wr_ready
                });
  end else begin : g_icache
    svc_rv_imem_cache_if imem_cache_if (
        .clk  (clk),
        .rst_n(rst_n),

        .imem_ren  (imem_ren),
        .imem_raddr(imem_raddr),
        .imem_rdata(imem_rdata),

        .imem_stall(imem_stall),

        .cache_rd_valid(icache_rd_valid),
        .cache_rd_addr (icache_rd_addr),
        .cache_rd_ready(icache_rd_ready),

        .cache_rd_data      (icache_rd_data),
        .cache_rd_data_valid(icache_rd_data_valid),
        .cache_rd_hit       (icache_rd_hit)
    );

    svc_cache_axi #(
        .CACHE_SIZE_BYTES(CACHE_SIZE_BYTES),
        .CACHE_ADDR_WIDTH(32),
        .CACHE_LINE_BYTES(CACHE_LINE_BYTES),
        .TWO_WAY         (CACHE_TWO_WAY),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH    (ARB_INTERNAL_ID_WIDTH)
    ) icache (
        .clk  (clk),
        .rst_n(rst_n),

        .rd_valid     (icache_rd_valid),
        .rd_addr      (icache_rd_addr),
        .rd_ready     (icache_rd_ready),
        .rd_data      (icache_rd_data),
        .rd_data_valid(icache_rd_data_valid),
        .rd_hit       (icache_rd_hit),

        .wr_valid(1'b0),
        .wr_ready(icache_wr_ready),
        .wr_addr (32'h0),
        .wr_data (32'h0),
        .wr_strb (4'h0),

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

    `SVC_UNUSED({icache_wr_ready, imem_rdata_bram});
  end

  //
  // Data memory path
  //
  // DCACHE_ENABLE=1: D$ backed by AXI
  // DCACHE_ENABLE=0: BRAM backed by internal memory (I/O bypass uses bit 31)
  //
  if (DCACHE_ENABLE != 0) begin : g_dcache
    assign bram_ren = 1'b0;
    assign bram_wen = 1'b0;

    //
    // Mux CPU vs debug writes - debug when CPU stalled
    //
    logic        eff_dmem_we;
    logic [31:0] eff_dmem_waddr;
    logic [31:0] eff_dmem_wdata;
    logic [ 3:0] eff_dmem_wstrb;

    assign eff_dmem_we = cpu_stall ? dbg_dmem_wen : dmem_wen;
    assign
        eff_dmem_waddr = cpu_stall ? 32'({dbg_dmem_waddr, 2'b00}) : dmem_waddr;
    assign eff_dmem_wdata = cpu_stall ? dbg_dmem_wdata : dmem_wdata;
    assign eff_dmem_wstrb = cpu_stall ? dbg_dmem_wstrb : dmem_wstrb;

    //
    // Data cache interface signals
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

    svc_rv_dmem_cache_if dmem_cache_if (
        .clk  (clk),
        .rst_n(rst_n),

        .dmem_ren  (dmem_ren),
        .dmem_raddr(dmem_raddr),
        .dmem_rdata(dmem_rdata),

        .dmem_we   (eff_dmem_we),
        .dmem_waddr(eff_dmem_waddr),
        .dmem_wdata(eff_dmem_wdata),
        .dmem_wstrb(eff_dmem_wstrb),

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

    // BRAM/IO signals not used when DCACHE_ENABLE=1
    assign io_sel_rd    = 1'b0;
    assign io_sel_rd_p1 = 1'b0;
    assign io_sel_wr    = 1'b0;
    `SVC_UNUSED({bram_rdata, io_sel_rd, io_sel_rd_p1, io_sel_wr});
  end else begin : g_dmem_bram
    assign dmem_stall = 1'b0;

    assign io_sel_rd  = dmem_raddr[31];
    assign io_sel_wr  = dmem_waddr[31];

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        io_sel_rd_p1 <= 1'b0;
      end else if (dmem_ren) begin
        io_sel_rd_p1 <= io_sel_rd;
      end
    end

    assign bram_ren   = dmem_ren && !io_sel_rd;
    assign io_ren     = dmem_ren && io_sel_rd;
    assign io_raddr   = dmem_raddr;
    assign dmem_rdata = io_sel_rd_p1 ? io_rdata : bram_rdata;

    assign bram_wen   = dmem_wen && !io_sel_wr;
    assign io_wen     = dmem_wen && io_sel_wr;
    assign io_waddr   = dmem_waddr;
    assign io_wdata   = dmem_wdata;
    assign io_wstrb   = dmem_wstrb;

    svc_axi_null #(
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_ID_WIDTH  (ARB_INTERNAL_ID_WIDTH)
    ) dcache_null (
        .clk  (clk),
        .rst_n(rst_n),

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
  end

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
