`ifndef SVC_RV_RISCV_DV_TB_SV
`define SVC_RV_RISCV_DV_TB_SV

`include "svc.sv"

`include "svc_rv_soc_bram.sv"

//
// riscv-dv Verilator testbench wrapper for SVC RISC-V processor
//
// This module wraps the SVC SOC and provides:
// - Clock/reset inputs
// - RVFI outputs for trace generation
// - Termination signals (ebreak, trap)
// - IO write signals for tohost detection
//
// Memory is initialized via IMEM_INIT parameter (Verilog hex file)
//
module svc_rv_riscv_dv_tb #(
    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n,

    //
    // Termination signals
    //
    output logic ebreak,
    output logic trap,

    //
    // IO write interface (for tohost detection)
    //
    output logic        io_wen,
    output logic [31:0] io_waddr,
    output logic [31:0] io_wdata,

    //
    // RVFI outputs for trace logging
    //
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [31:0] rvfi_rd_wdata,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,
    output logic        rvfi_mem_valid,
    output logic        rvfi_mem_instr,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata
);
  logic [31:0] io_rdata;
  assign io_rdata = 32'h0;

  //
  // SVC RISC-V SOC with BRAM
  //
  // 128KB memory for riscv-dv tests (32768 words)
  //
  svc_rv_soc_bram #(
      .XLEN       (32),
      .IMEM_DEPTH (32768),
      .DMEM_DEPTH (32768),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (0),
      .BTB_ENABLE (0),
      .RAS_ENABLE (0),
      .EXT_ZMMUL  (0),
      .EXT_M      (1),
      .RESET_PC   (32'h00010000),
      .IMEM_INIT  (IMEM_INIT),
      .DMEM_INIT  ("")
  ) soc (
      .clk  (clk),
      .rst_n(rst_n),

      .io_ren  (),
      .io_raddr(),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(),

      .ebreak(ebreak),
      .trap  (trap),

      .rvfi_valid    (rvfi_valid),
      .rvfi_order    (rvfi_order),
      .rvfi_insn     (rvfi_insn),
      .rvfi_pc_rdata (rvfi_pc_rdata),
      .rvfi_pc_wdata (rvfi_pc_wdata),
      .rvfi_rs1_addr (rvfi_rs1_addr),
      .rvfi_rs2_addr (rvfi_rs2_addr),
      .rvfi_rd_addr  (rvfi_rd_addr),
      .rvfi_rs1_rdata(rvfi_rs1_rdata),
      .rvfi_rs2_rdata(rvfi_rs2_rdata),
      .rvfi_rd_wdata (rvfi_rd_wdata),
      .rvfi_trap     (rvfi_trap),
      .rvfi_halt     (rvfi_halt),
      .rvfi_intr     (rvfi_intr),
      .rvfi_mode     (rvfi_mode),
      .rvfi_ixl      (rvfi_ixl),
      .rvfi_mem_valid(rvfi_mem_valid),
      .rvfi_mem_instr(rvfi_mem_instr),
      .rvfi_mem_addr (rvfi_mem_addr),
      .rvfi_mem_rmask(rvfi_mem_rmask),
      .rvfi_mem_wmask(rvfi_mem_wmask),
      .rvfi_mem_rdata(rvfi_mem_rdata),
      .rvfi_mem_wdata(rvfi_mem_wdata)
  );

endmodule

`endif
