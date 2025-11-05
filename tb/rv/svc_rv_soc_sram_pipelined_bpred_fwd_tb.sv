`include "svc_unit.sv"

`include "svc_mem_sram.sv"
`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_bpred_fwd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with SRAM, pipelined mode, forwarding, and branch prediction
  //
  // This is the most aggressive configuration with best expected CPI.
  // With JAL early resolution in ID stage and MEM->EX load forwarding,
  // we achieve near-optimal performance.
  //
  localparam real alu_indep_max_cpi = 1.17;
  localparam real alu_chain_max_cpi = 1.38;
  localparam real br_taken_max_cpi = 2.5;
  localparam real br_not_taken_max_cpi = 2.25;
  localparam real load_use_max_cpi = 1.75;
  localparam real mixed_alu_max_cpi = 1.34;
  localparam real fib12_max_cpi = 1.22;
  localparam real fib100_max_cpi = 1.18;
  localparam real bubble_max_cpi = 1.41;
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
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (1)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

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
  svc_mem_sram #(
      .DW(32),
      .AW(IO_AW)
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
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_pipelined_bpred_fwd_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
