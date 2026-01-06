`include "svc_unit.sv"

`include "svc_mem_bram.sv"
`include "svc_rv_soc_bram.sv"

module svc_rv_soc_bram_zmmul_fwd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;
  localparam int IO_AW = 10;

  //
  // CPI expectations with BRAM memories, Zmmul, and forwarding
  //
  // With forwarding, EX and MEM hazards are handled without stalling.
  // Zmmul results can be forwarded just like ALU results, maintaining
  // similar performance to baseline forwarding configuration.
  //
  // BRAM has 1-cycle read latency, so load-use hazards are more expensive
  // than SRAM configs. However, ALU forwarding should still provide benefit.
  //
  localparam real alu_indep_max_cpi = 1.50;
  localparam real alu_chain_max_cpi = 1.40;
  localparam real br_taken_max_cpi = 2.55;
  localparam real br_not_taken_max_cpi = 1.80;
  localparam real load_use_max_cpi = 2.30;
  localparam real mixed_alu_max_cpi = 1.35;
  localparam real function_calls_max_cpi = 2.5;
  localparam real fib12_max_cpi = 1.52;
  localparam real fib100_max_cpi = 1.52;
  localparam real bubble_max_cpi = 1.58;
  localparam real forward_taken_loop_max_cpi = 3.0;
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
  // System under test - pipelined with Zmmul and forwarding
  //
  svc_rv_soc_bram #(
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .EXT_ZMMUL  (1)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .dbg_urx_valid(1'b0),
      .dbg_urx_data (8'h0),
      .dbg_urx_ready(),
      .dbg_utx_valid(),
      .dbg_utx_data (),
      .dbg_utx_ready(1'b1),


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
  `include "svc_rv_soc_test_defs_m.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_zmmul_fwd_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `include "svc_rv_soc_test_list_m.svh"
  `TEST_SUITE_END();

endmodule
