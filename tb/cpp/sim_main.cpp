// Generic Verilator simulation wrapper for SoC simulations
//
// This provides the main() entry point for Verilator-compiled simulations.
// It handles:
// - Command line plusargs
// - Simulation execution with timing
// - VCD trace generation (optional)
// - Non-blocking stdin for UART input
//
// The actual simulation logic (clock generation, reset, watchdog, etc.)
// is handled by the SystemVerilog svc_soc_sim module.

#include <memory>
#include <fcntl.h>
#include <unistd.h>
#include <poll.h>

#include "verilated.h"

// The Verilator-generated header - set by -CFLAGS during build
#include SIM_HEADER

// Global context
static std::unique_ptr<VerilatedContext> ctx;
static std::unique_ptr<SIM_TOP> top;

// DPI function for non-blocking stdin read
// Returns -1 if no data available, otherwise the character
extern "C" int svc_stdin_getc() {
    struct pollfd pfd;
    pfd.fd = STDIN_FILENO;
    pfd.events = POLLIN;

    if (poll(&pfd, 1, 0) > 0) {
        if (pfd.revents & POLLIN) {
            char c;
            if (read(STDIN_FILENO, &c, 1) == 1) {
                return (int)(unsigned char)c;
            }
        }
    }
    return -1;
}

// DPI function to check if stdin has data
extern "C" int svc_stdin_ready() {
    struct pollfd pfd;
    pfd.fd = STDIN_FILENO;
    pfd.events = POLLIN;

    return (poll(&pfd, 1, 0) > 0 && (pfd.revents & POLLIN)) ? 1 : 0;
}

int main(int argc, char** argv) {
    // Create context
    ctx = std::make_unique<VerilatedContext>();
    ctx->commandArgs(argc, argv);

    // Create DUT
    top = std::make_unique<SIM_TOP>(ctx.get());

    // Set stdin to non-blocking mode for DPI stdin functions
    int stdin_flags = fcntl(STDIN_FILENO, F_GETFL, 0);
    fcntl(STDIN_FILENO, F_SETFL, stdin_flags | O_NONBLOCK);

    // Run simulation until $finish
    // With --timing, Verilator uses coroutine-based scheduling.
    // We need to call eval_step() repeatedly and let it advance time.
    while (!ctx->gotFinish()) {
        // eval_step runs until the next time quantum
        top->eval_step();
        // Check if simulation needs to advance time
        if (!top->eventsPending()) break;
        ctx->time(top->nextTimeSlot());
        top->eval_end_step();
    }

    // Restore stdin flags
    fcntl(STDIN_FILENO, F_SETFL, stdin_flags);

    // Cleanup
    top->final();
    return 0;
}
