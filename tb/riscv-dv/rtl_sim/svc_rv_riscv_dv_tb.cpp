// SVC RISC-V riscv-dv Verilator testbench driver
//
// This C++ driver:
// - Runs simulation until ebreak, tohost write, or timeout
// - Outputs RVFI traces in riscv-dv CSV format
//
// Memory is initialized via Verilog parameter at compile time.

#include <verilated.h>
#include "Vsvc_rv_riscv_dv_tb.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

// HTIF tohost address (must match link.ld)
constexpr uint32_t TOHOST_ADDR = 0x80001000;

// Simulation context
vluint64_t main_time = 0;

double sc_time_stamp() {
    return main_time;
}

// Register name lookup
const char* reg_name(int addr) {
    static const char* names[] = {
        "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
        "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
        "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
        "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
    };
    if (addr >= 0 && addr < 32) {
        return names[addr];
    }
    return "x?";
}

// Clock the design for one cycle
void clock_cycle(Vsvc_rv_riscv_dv_tb* tb) {
    tb->clk = 0;
    tb->eval();
    main_time++;

    tb->clk = 1;
    tb->eval();
    main_time++;
}

int main(int argc, char** argv) {
    // Parse command line
    Verilated::commandArgs(argc, argv);

    // Get plusargs
    const char* trace_file = "trace.csv";
    int max_cycles = 1000000;

    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "+trace=", 7) == 0) {
            trace_file = argv[i] + 7;
        } else if (strncmp(argv[i], "+max_cycles=", 12) == 0) {
            max_cycles = atoi(argv[i] + 12);
        }
    }

    // Create model
    Vsvc_rv_riscv_dv_tb* tb = new Vsvc_rv_riscv_dv_tb;

    // Open trace file
    FILE* trace_fd = fopen(trace_file, "w");
    if (!trace_fd) {
        fprintf(stderr, "ERROR: Cannot open trace file: %s\n", trace_file);
        return 1;
    }

    // Write CSV header
    fprintf(trace_fd, "pc,instr,gpr,csr,binary,mode,instr_str,operand,pad\n");

    // Initialize
    tb->clk = 0;
    tb->rst_n = 0;
    tb->eval();

    // Hold reset for a few cycles
    for (int i = 0; i < 10; i++) {
        clock_cycle(tb);
    }

    // Release reset
    tb->rst_n = 1;

    // Main simulation loop
    int cycle_count = 0;
    bool done = false;
    bool trap_seen = false;
    int result = 0;

    while (!done && cycle_count < max_cycles) {
        // Clock cycle
        tb->clk = 0;
        tb->eval();
        main_time++;

        tb->clk = 1;
        tb->eval();
        main_time++;

        // Check RVFI valid and log trace
        if (tb->rvfi_valid) {
            char gpr_str[64] = "";
            if (tb->rvfi_rd_addr != 0) {
                snprintf(gpr_str, sizeof(gpr_str), "%s:0x%08x",
                         reg_name(tb->rvfi_rd_addr), tb->rvfi_rd_wdata);
            }

            fprintf(trace_fd, "%08x,,%s,,%08x,3,,,\n",
                    tb->rvfi_pc_rdata,
                    gpr_str,
                    tb->rvfi_insn);
        }

        // Check termination conditions
        if (tb->ebreak) {
            printf("PASS: ebreak at cycle %d\n", cycle_count);
            done = true;
            result = 0;
        } else if (tb->io_wen && tb->io_waddr == TOHOST_ADDR) {
            // HTIF tohost write - check exit code
            // Value 1 = pass, other non-zero = fail (value >> 1 is exit code)
            uint32_t tohost_val = tb->io_wdata;
            if (tohost_val == 1) {
                printf("PASS: tohost=1 at cycle %d\n", cycle_count);
                result = 0;
            } else {
                printf("FAIL: tohost=0x%08x (exit code %d) at cycle %d\n",
                       tohost_val, tohost_val >> 1, cycle_count);
                result = 1;
            }
            done = true;
        } else if (tb->trap && !trap_seen) {
            // Log trap but don't exit - let trace comparison show divergence
            printf("TRAP: cycle %d, PC=0x%08x, insn=0x%08x\n",
                   cycle_count, tb->rvfi_pc_rdata, tb->rvfi_insn);
            trap_seen = true;
            result = 1;
        }

        cycle_count++;
    }

    if (!done) {
        printf("FAIL: timeout at cycle %d\n", cycle_count);
        result = 1;
    }

    // Cleanup
    fclose(trace_fd);
    tb->final();
    delete tb;

    return result;
}
