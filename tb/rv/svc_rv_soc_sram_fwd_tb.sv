`include "svc_unit.sv"

`include "svc_mem_sram.sv"
`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_fwd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with SRAM, pipelined mode, and forwarding
  //
  // With MEM->EX ALU and load data forwarding, hazards are handled without
  // stalling. Major improvements in ALU chains, mixed ALU, and load-use
  // workloads.
  //
  // Note: Branch penalties (2 cycles for taken branches) are unavoidable
  // without branch prediction, so workloads with many branches will still
  // show elevated CPI even with perfect data forwarding.
  //
  localparam real alu_indep_max_cpi = 1.34;
  localparam real alu_chain_max_cpi = 1.26;
  localparam real br_taken_max_cpi = 2.05;
  localparam real br_not_taken_max_cpi = 1.55;
  localparam real load_use_max_cpi = 1.55;
  localparam real mixed_alu_max_cpi = 1.25;
  localparam real function_calls_max_cpi = 2.0;
  localparam real fib12_max_cpi = 1.35;
  localparam real fib100_max_cpi = 1.34;
  localparam real bubble_max_cpi = 1.30;
  localparam real forward_taken_loop_max_cpi = 2.35;
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
      .FWD        (1)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

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
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_fwd_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
