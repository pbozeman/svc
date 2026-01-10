`ifndef SVC_RV_SOC_BRAM_SV
`define SVC_RV_SOC_BRAM_SV

`include "svc.sv"

`include "svc_mem_bram.sv"
`include "svc_rv.sv"
`include "svc_rv_dbg_bridge.sv"

//
// RISC-V SoC with BRAM memories
//
// RISC-V core with separate instruction and data BRAMs.
// BRAMs have 1-cycle read latency (registered reads).
//
// Pipeline configuration:
// - MEM_TYPE=MEM_TYPE_BRAM: Use BRAM timing (1-cycle latency)
// - All pipeline registers enabled for fully-pipelined operation
// - FWD_REGFILE=1: Enabled to reduce hazards
//
module svc_rv_soc_bram #(
    parameter int XLEN          = 32,
    parameter int IMEM_DEPTH    = 1024,
    parameter int DMEM_DEPTH    = 1024,
    parameter int PIPELINED     = 1,
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

    parameter IMEM_INIT = "",
    parameter DMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    //
    // Debug UART interface (active when DEBUG_ENABLED=1)
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
  localparam int DMEM_AW = $clog2(DMEM_DEPTH);

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

  //
  // CPU control signals
  //
  logic               cpu_rst_n;
  logic               cpu_stall;

  assign cpu_rst_n = rst_n && dbg_rst_n;
  assign cpu_stall = dbg_stall;

  //
  // Memory interface signals
  //
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;
  logic        imem_ren;

  logic        dmem_ren;
  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_wen;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  //
  // BRAM interface signals
  //
  logic        bram_ren;
  logic [31:0] bram_rdata;
  logic        bram_wen;

  //
  // Address decode signals
  //
  logic        io_sel_rd;
  logic        io_sel_rd_p1;
  logic        io_sel_wr;

  `include "svc_rv_defs.svh"

  //
  // Debug bridge (optional)
  //
  if (DEBUG_ENABLED != 0) begin : g_dbg
    svc_rv_dbg_bridge #(
        .IMEM_ADDR_WIDTH(IMEM_AW),
        .DMEM_ADDR_WIDTH(DMEM_AW),
        .IMEM_BASE_ADDR (32'h0000_0000),
        .DMEM_BASE_ADDR (32'(IMEM_DEPTH) << 2)
    ) dbg_bridge (
        .clk  (clk),
        .rst_n(rst_n),

        .urx_valid(dbg_urx_valid),
        .urx_data (dbg_urx_data),
        .urx_ready(dbg_urx_ready),

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
        .dbg_dmem_busy (1'b0),

        // Read interface - not used for BRAM-only SoC (tie to defaults)
        .dbg_dmem_ren        (),
        .dbg_dmem_raddr      (),
        .dbg_dmem_rdata      (32'h0),
        .dbg_dmem_rdata_valid(1'b1)
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
    assign dbg_urx_ready  = 1'b0;
    assign dbg_utx_valid  = 1'b0;
    assign dbg_utx_data   = 8'h0;

    `SVC_UNUSED({dbg_urx_valid, dbg_urx_data, dbg_utx_ready})
  end

  //
  // Address decode
  //
  assign io_sel_rd = dmem_raddr[31];
  assign io_sel_wr = dmem_waddr[31];

  //
  // Register read select since we need to use it for the response mux
  //
  always_ff @(posedge clk) begin
    if (!cpu_rst_n) begin
      io_sel_rd_p1 <= 1'b0;
    end else if (dmem_ren) begin
      io_sel_rd_p1 <= io_sel_rd;
    end
  end

  //
  // Read path routing
  //
  assign bram_ren   = dmem_ren && !io_sel_rd;
  assign io_ren     = dmem_ren && io_sel_rd;
  assign io_raddr   = dmem_raddr;
  assign dmem_rdata = io_sel_rd_p1 ? io_rdata : bram_rdata;

  //
  // Write path routing
  //
  assign bram_wen   = dmem_wen && !io_sel_wr;
  assign io_wen     = dmem_wen && io_sel_wr;
  assign io_waddr   = dmem_waddr;
  assign io_wdata   = dmem_wdata;
  assign io_wstrb   = dmem_wstrb;

  //
  // RISC-V core
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

      .dmem_stall(cpu_stall),
      .imem_stall(cpu_stall),

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
  // Instruction memory (BRAM) with debug write port
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
      .wr_addr(32'({dbg_imem_waddr, 2'b00})),
      .wr_data(dbg_imem_wdata),
      .wr_strb(dbg_imem_wstrb),
      .wr_en  (dbg_imem_wen)
  );

  //
  // Data memory (BRAM) with debug write port
  //
  // CPU writes take priority; debug writes only when CPU not writing
  //
  logic        dmem_wr_en;
  logic [31:0] dmem_wr_addr;
  logic [31:0] dmem_wr_data;
  logic [ 3:0] dmem_wr_strb;

  assign dmem_wr_en   = bram_wen || dbg_dmem_wen;
  assign dmem_wr_addr = bram_wen ? dmem_waddr : 32'({{dbg_dmem_waddr, 2'b00}});
  assign dmem_wr_data = bram_wen ? dmem_wdata : dbg_dmem_wdata;
  assign dmem_wr_strb = bram_wen ? dmem_wstrb : dbg_dmem_wstrb;

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

      .wr_en  (dmem_wr_en),
      .wr_addr(dmem_wr_addr),
      .wr_data(dmem_wr_data),
      .wr_strb(dmem_wr_strb)
  );

endmodule

`endif
