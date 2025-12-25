`ifndef SVC_RV_SOC_BRAM_CACHE_SV
`define SVC_RV_SOC_BRAM_CACHE_SV

`include "svc.sv"

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
    parameter int XLEN        = 32,
    parameter int IMEM_DEPTH  = 1024,
    parameter int PIPELINED   = 1,
    parameter int FWD_REGFILE = 1,
    parameter int FWD         = 0,
    parameter int BPRED       = 0,
    parameter int BTB_ENABLE  = 0,
    parameter int BTB_ENTRIES = 16,
    parameter int RAS_ENABLE  = 0,
    parameter int RAS_DEPTH   = 8,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0,
    parameter int PC_REG      = 0,

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

  logic        cache_wr_valid;
  logic        cache_wr_ready;
  logic [31:0] cache_wr_addr;
  logic [31:0] cache_wr_data;
  logic [ 3:0] cache_wr_strb;

  `include "svc_rv_defs.svh"

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
      .AXI_ID_WIDTH    (AXI_ID_WIDTH)
  ) dcache (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_valid     (cache_rd_valid),
      .rd_ready     (cache_rd_ready),
      .rd_addr      (cache_rd_addr),
      .rd_data      (cache_rd_data),
      .rd_data_valid(cache_rd_data_valid),
      .rd_hit       (),

      .wr_valid(cache_wr_valid),
      .wr_ready(cache_wr_ready),
      .wr_addr (cache_wr_addr),
      .wr_data (cache_wr_data),
      .wr_strb (cache_wr_strb),

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
      .m_axi_bready(m_axi_bready)
  );

endmodule

`endif
