// Generic Verilator testbench wrapper
//
// Simple wrapper that runs the testbench to completion.
// Clock generation, reset, and test logic are all in SystemVerilog.

#include <memory>

#include "verilated.h"

// The Verilator-generated header - set by -CFLAGS during build
#include TB_HEADER

int main(int argc, char **argv) {
  // Create context
  auto ctx = std::make_unique<VerilatedContext>();
  ctx->commandArgs(argc, argv);

  // Create DUT
  auto top = std::make_unique<TB_TOP>(ctx.get());

  // Run simulation until $finish
  while (!ctx->gotFinish()) {
    top->eval_step();
    if (!top->eventsPending())
      break;
    ctx->time(top->nextTimeSlot());
    top->eval_end_step();
  }

  // Cleanup
  top->final();
  return 0;
}
