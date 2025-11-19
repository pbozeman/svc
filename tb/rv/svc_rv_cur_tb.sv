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
    uut.imem.mem[0]  = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[1]  = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[2]  = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[3]  = 32'h00000013;  // addi x0,x0,0
    uut.imem.mem[4]  = 32'h3c0d5c83;  // lhu x25,960(x26)
    uut.imem.mem[5]  = 32'h69040817;  // auipc x16,0x69040
    uut.imem.mem[6]  = 32'h0160e403;  // .insn 4, 0x0160e403
    uut.imem.mem[7]  = 32'hff883c03;  // .insn 4, 0xff883c03
    uut.imem.mem[8]  = 32'hff841133;  // .insn 4, 0xff841133
    uut.imem.mem[9]  = 32'hc0247473;  // csrrci x8,instret,8
    uut.imem.mem[10] = 32'hc089dc63;  // bge x19,x8,0xfffff440
    uut.imem.mem[11] = 32'ha18b21f3;  // csrrs x3,0xa18,x22
    uut.imem.mem[12] = 32'h528c2173;  // csrrs x2,0x528,x24
    uut.imem.mem[13] = 32'h20890103;  // lb x2,520(x18)
    uut.imem.mem[14] = 32'h00500033;  // add x0,x0,x5
    uut.imem.mem[15] = 32'h00100073;  // ebreak

    `CHECK_WAIT_FOR(clk, ebreak, 128);
    `CHECK_TRUE(ebreak);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_cur_tb);
  `TEST_CASE(test_run);
  `TEST_SUITE_END();

endmodule
