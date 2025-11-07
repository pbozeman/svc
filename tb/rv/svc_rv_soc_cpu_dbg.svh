//
// CPU pipeline execution monitoring
//
// Provides optional debug display of instruction execution for RISC-V SOC
// testbenches. Controlled by +SVC_CPU_DBG plusarg.
//
// NOTE: This include is designed for BRAM-based SOC testbenches which have
// io_ren signal. SRAM-based SOCs do not have io_ren and will need a modified
// version.
//
// Usage:
//   `include "svc_rv_soc_cpu_dbg.svh" in testbench after UUT instantiation
//

`include "svc_rv_dasm.svh"

logic cpu_dbg_enabled;

initial begin
  if ($test$plusargs("SVC_CPU_DBG")) begin
    cpu_dbg_enabled = 1'b1;
  end else begin
    cpu_dbg_enabled = 1'b0;
  end
end

always @(posedge clk) begin
  if (rst_n && cpu_dbg_enabled) begin
    $display("[%12t] %-4s %08x  %-28s  %08x %08x -> %08x", $time, "",
             uut.cpu.pc_ex, dasm_inst(uut.cpu.instr_ex), uut.cpu.alu_a_ex,
             uut.cpu.alu_b_ex, uut.cpu.alu_result_ex);

    if (io_ren) begin
      $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MR:",
               uut.cpu.pc_plus4_mem - 4, "", uut.cpu.alu_result_mem, "",
               io_rdata);
    end else if (io_wen) begin
      $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MW:",
               uut.cpu.pc_plus4_mem - 4, "", uut.cpu.alu_result_mem, "",
               io_wdata);
    end
  end
end
