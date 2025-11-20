`include "svc_unit.sv"

`include "svc_mem_bram.sv"
`include "svc_rv_soc_bram.sv"

module svc_rv_soc_bram_btb_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with BRAM memories and branch prediction with BTB
  //
  // With JAL early resolution, BTFNT prediction, and dynamic BTB
  // BRAM latency still adds overhead compared to SRAM
  // BTB has learning overhead for initial branch executions
  //
  localparam real alu_indep_max_cpi = 1.01;
  localparam real alu_chain_max_cpi = 2.50;
  localparam real br_taken_max_cpi = 2.05;
  localparam real br_not_taken_max_cpi = 2.05;
  localparam real load_use_max_cpi = 2.05;
  localparam real mixed_alu_max_cpi = 2.34;
  localparam real function_calls_max_cpi = 2.20;
  localparam real fib12_max_cpi = 1.37;
  localparam real fib100_max_cpi = 1.34;
  localparam real bubble_max_cpi = 1.90;
  localparam real forward_taken_loop_max_cpi = 1.75;
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
  // System under test
  //
  svc_rv_soc_bram #(
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .BPRED      (1),
      .BTB_ENABLE (1),
      .BTB_ENTRIES(16)
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

      .ebreak(ebreak),
      .trap  ()
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

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_btb_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
