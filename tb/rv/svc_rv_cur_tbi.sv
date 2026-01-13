`define RISCV_FORMAL 1

`include "svc_unit.sv"

`include "svc_rv_soc_bram.sv"

//
// Quick regression testbench for debugging specific instruction sequences
//
// verilator lint_off: UNUSEDSIGNAL
module svc_rv_cur_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_DEPTH = 2 ** 10;
  localparam int DMEM_DEPTH = 2 ** 10;

  logic ebreak;

  //
  // System under test
  //
  svc_rv_soc_bram #(
      .XLEN       (32),
      .IMEM_DEPTH (IMEM_DEPTH),
      .DMEM_DEPTH (DMEM_DEPTH),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (1),
      .BTB_ENABLE (1),
      .BTB_ENTRIES(32),
      .RAS_ENABLE (0),
      .EXT_ZMMUL  (0),
      .EXT_M      (0)

  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .dbg_urx_valid(1'b0),
      .dbg_urx_data (8'h0),
      .dbg_urx_ready(),
      .dbg_utx_valid(),
      .dbg_utx_data (),
      .dbg_utx_ready(1'b1),

      .io_ren  (),
      .io_raddr(),
      .io_rdata(32'h0),

      .io_wen  (),
      .io_waddr(),
      .io_wdata(),
      .io_wstrb(),

      .ebreak(ebreak),
      .trap  (),

      .rvfi_valid    (),
      .rvfi_order    (),
      .rvfi_insn     (),
      .rvfi_pc_rdata (),
      .rvfi_pc_wdata (),
      .rvfi_rs1_addr (),
      .rvfi_rs2_addr (),
      .rvfi_rd_addr  (),
      .rvfi_rs1_rdata(),
      .rvfi_rs2_rdata(),
      .rvfi_rd_wdata (),
      .rvfi_trap     (),
      .rvfi_halt     (),
      .rvfi_intr     (),
      .rvfi_mode     (),
      .rvfi_ixl      (),
      .rvfi_mem_valid(),
      .rvfi_mem_instr(),
      .rvfi_mem_addr (),
      .rvfi_mem_rmask(),
      .rvfi_mem_wmask(),
      .rvfi_mem_rdata(),
      .rvfi_mem_wdata()
  );

  //
  // Hack in a failed formal runs here for debugging
  //
  task automatic test_run();
    //
    // Fill in instructions here to debug
    //
    uut.imem.mem[0] = 32'h00000013;
    uut.imem.mem[1] = 32'h00100073;

    `CHECK_WAIT_FOR(clk, uut.cpu.rvfi_valid && uut.cpu.rvfi_halt);
    `TICK(clk);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_cur_tbi);
  `TEST_CASE(test_run);
  `TEST_SUITE_END();

endmodule
