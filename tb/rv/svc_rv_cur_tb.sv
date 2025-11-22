`define RISCV_FORMAL 1

`include "svc_unit.sv"

`include "svc_mem_sram.sv"
`include "svc_rv_soc_sram.sv"

//
// Quick regression testbench for debugging specific instruction sequences
//
// verilator lint_off: UNUSEDSIGNAL
module svc_rv_cur_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;

  logic ebreak;

  //
  // System under test
  //
  svc_rv_soc_sram #(
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (1),
      .BTB_ENABLE (1),
      .RAS_ENABLE (0),
      .EXT_ZMMUL  (0),
      .EXT_M      (0)

  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .io_raddr(),
      .io_rdata(32'h0),

      .io_wen  (),
      .io_waddr(),
      .io_wdata(),
      .io_wstrb(),

      .ebreak(ebreak),
      .trap  ()
  );

  //
  // Hack in a failed formal runs here for debugging
  //
  task automatic test_run();
    int timeout;

    //
    // Fill in instructions here to debug
    //
    uut.imem.mem[0] = 32'hffdff36f;
    uut.imem.mem[1] = 32'h80635213;
    uut.imem.mem[2] = 32'h01e20413;
    uut.imem.mem[3] = 32'h00100073;

    `CHECK_WAIT_FOR(clk, uut.cpu.rvfi_valid && uut.cpu.rvfi_halt);
    `TICK(clk);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_cur_tb);
  `TEST_CASE(test_run);
  `TEST_SUITE_END();

endmodule
