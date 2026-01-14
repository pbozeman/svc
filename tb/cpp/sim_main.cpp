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

#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <memory>
#include <poll.h>
#include <pty.h>
#include <unistd.h>

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

// PTY support for external tool connection (e.g., Python loader)
static int pty_master_fd = -1;
static char pty_slave_path[256] = {0};

// DPI function to create a PTY
// Returns 1 on success, 0 on failure
// Path is printed to stdout (simpler than passing string back to SV)
extern "C" int svc_pty_create(int imem_depth) {
  int slave_fd;

  if (openpty(&pty_master_fd, &slave_fd, pty_slave_path, nullptr, nullptr) <
      0) {
    perror("openpty");
    return 0;
  }

  // Set master to non-blocking
  int flags = fcntl(pty_master_fd, F_GETFL, 0);
  fcntl(pty_master_fd, F_SETFL, flags | O_NONBLOCK);

  // Close slave - external tool will open it
  close(slave_fd);

  // Print the path for the user
  printf("\n");
  printf("PTY created: %s\n", pty_slave_path);
  printf("Connect with:\n");
  printf("./scripts/rv_loader -p %s --imem-depth %d --run <program.elf>\n",
         pty_slave_path, imem_depth);
  printf("\n");
  fflush(stdout);

  return 1;
}

// DPI function to read a byte from PTY (non-blocking)
// Returns -1 if no data available, otherwise the byte
extern "C" int svc_pty_getc() {
  if (pty_master_fd < 0)
    return -1;

  struct pollfd pfd;
  pfd.fd = pty_master_fd;
  pfd.events = POLLIN;

  if (poll(&pfd, 1, 0) > 0 && (pfd.revents & POLLIN)) {
    unsigned char c;
    if (read(pty_master_fd, &c, 1) == 1) {
      return (int)c;
    }
  }
  return -1;
}

// DPI function to write a byte to PTY
extern "C" void svc_pty_putc(int c) {
  if (pty_master_fd < 0)
    return;
  unsigned char ch = (unsigned char)c;
  [[maybe_unused]] ssize_t result = write(pty_master_fd, &ch, 1);
}

// DPI function to check if PTY has data
extern "C" int svc_pty_ready() {
  if (pty_master_fd < 0)
    return 0;

  struct pollfd pfd;
  pfd.fd = pty_master_fd;
  pfd.events = POLLIN;

  return (poll(&pfd, 1, 0) > 0 && (pfd.revents & POLLIN)) ? 1 : 0;
}

int main(int argc, char **argv) {
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
    if (!top->eventsPending())
      break;
    ctx->time(top->nextTimeSlot());
    top->eval_end_step();
  }

  // Restore stdin flags
  fcntl(STDIN_FILENO, F_SETFL, stdin_flags);

  // Cleanup
  top->final();
  return 0;
}
