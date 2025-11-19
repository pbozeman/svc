`include "svc_unit.sv"

`include "svc_mem_sram.sv"
`include "svc_rv_soc_sram.sv"

//
// Quick regression testbench for debugging specific instruction sequences
//
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
      .BPRED      (0),
      .BTB_ENABLE (0),
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

      .ebreak(ebreak)
  );

  //
  // Hack in a failed formal runs here for debugging
  //
  task test_run();
    uut.imem.mem[0] = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[1] = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[2] = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[3] = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[4] = 32'hc1ffbd43;  // fmadd.s f26,f31,f31,f24,rup
    uut.imem.mem[5] = 32'hd9bc353b;  // .insn 4, 0xd9bc353b
    uut.imem.mem[6] = 32'h80ad2d22;  // c.fldsp f26,8(x2); c.srli x9,0xb
    uut.imem.mem[7] = 32'h7fac1fa3;  // sh x26,2047(x24)
    uut.imem.mem[8] = 32'h00100073;  // ebreak

    `CHECK_WAIT_FOR(clk, ebreak, 128);
    `CHECK_TRUE(ebreak);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_cur_tb);
  `TEST_CASE(test_run);
  `TEST_SUITE_END();

endmodule
