`include "svc_unit.sv"

`include "svc_mem_bram.sv"
`include "svc_rv_soc_bram.sv"

module svc_rv_soc_bram_all_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with all features enabled
  //
  // With forwarding, branch prediction with BTB, and M extension enabled.
  // This configuration provides the best performance with:
  // - FWD=1: EX and MEM hazards handled without stalling
  // - BPRED=1: Branch prediction reduces branch penalty
  // - BTB_ENABLE=1: Dynamic branch target buffer
  // - EXT_M=1: Hardware multiply/divide support
  //
  // This achieves near-ideal CPI (~1.0) for most instruction sequences.
  // Only load-use hazards and bubble sort have noticeable overhead.
  //
  localparam real alu_indep_max_cpi = 1.01;
  localparam real alu_chain_max_cpi = 1.01;
  localparam real br_taken_max_cpi = 1.01;
  localparam real br_not_taken_max_cpi = 1.01;
  localparam real load_use_max_cpi = 1.52;
  localparam real mixed_alu_max_cpi = 1.01;
  localparam real fib12_max_cpi = 1.08;
  localparam real fib100_max_cpi = 1.02;
  localparam real bubble_max_cpi = 1.31;
  localparam real forward_taken_loop_max_cpi = 1.20;
  logic        ebreak;

  //
  // MMIO interface signals
  //
  logic        io_ren;
  logic [31:0] io_raddr;
  logic [31:0] io_rdata;
  logic        io_wen;
  logic [31:0] io_waddr;
  logic [31:0] io_wdata;
  logic [ 3:0] io_wstrb;

  //
  // System under test - all features enabled
  //
  svc_rv_soc_bram #(
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (1),
      .BTB_ENABLE (1),
      .BTB_ENTRIES(16),
      .EXT_M      (1)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .io_ren  (io_ren),
      .io_raddr(io_raddr),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(io_wstrb),

      .ebreak(ebreak)
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

  `include "svc_rv_soc_test_defs.svh"
  `include "svc_rv_soc_test_defs_m.svh"
  `include "svc_rv_soc_test_defs_d.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_all_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `include "svc_rv_soc_test_list_m.svh"
  `include "svc_rv_soc_test_list_d.svh"
  `TEST_SUITE_END();

endmodule
