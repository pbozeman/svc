`include "svc_unit.sv"

`include "svc_mem_sram.sv"
`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_ras_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with SRAM, pipelined mode, no forwarding, with full branch prediction (BTB + RAS)
  //
  // BTB provides dynamic branch prediction, RAS improves return prediction
  // Combined BTB + RAS gives best prediction accuracy
  // SRAM zero-cycle latency provides better performance than BRAM
  //
  localparam real alu_indep_max_cpi = 1.15;
  localparam real alu_chain_max_cpi = 2.6;
  localparam real br_taken_max_cpi = 2.25;
  localparam real br_not_taken_max_cpi = 2.0;
  localparam real load_use_max_cpi = 2.2;
  localparam real mixed_alu_max_cpi = 2.4;
  localparam real function_calls_max_cpi = 1.85;
  localparam real fib12_max_cpi = 1.41;
  localparam real fib100_max_cpi = 1.38;
  localparam real bubble_max_cpi = 1.95;
  localparam real forward_taken_loop_max_cpi = 1.74;
  logic        ebreak;

  //
  // MMIO interface signals
  //
  logic [31:0] io_raddr;
  logic [31:0] io_rdata;
  logic        io_wen;
  logic [31:0] io_waddr;
  logic [31:0] io_wdata;
  logic [ 3:0] io_wstrb;

  //
  // System under test
  //
  svc_rv_soc_sram #(
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (0),
      .BPRED      (1),
      .BTB_ENABLE (1),
      .BTB_ENTRIES(16),
      .RAS_ENABLE (1),
      .RAS_DEPTH  (8)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .dbg_urx_valid(1'b0),
      .dbg_urx_data (8'h0),
      .dbg_urx_ready(),
      .dbg_utx_valid(),
      .dbg_utx_data (),
      .dbg_utx_ready(1'b1),


      .io_raddr(io_raddr),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(io_wstrb),

      .ebreak(ebreak),
      .trap  ()
  );

  //
  // Memory-mapped I/O memory
  //
  svc_mem_sram #(
      .DW   (32),
      .DEPTH(2 ** IO_AW)
  ) io_mem (
      .clk  (clk),
      .rst_n(rst_n),

      .rd_addr(io_raddr),
      .rd_data(io_rdata),

      .wr_en  (io_wen),
      .wr_addr(io_waddr),
      .wr_data(io_wdata),
      .wr_strb(io_wstrb)
  );

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_ras_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
