`ifndef SVC_RV_STALL_INJECTOR_SV
`define SVC_RV_STALL_INJECTOR_SV

`include "svc.sv"

//
// RISC-V Data Memory Stall Injector
//
// Injects random stalls on data memory accesses for testing CPU stall handling.
// Uses $urandom_range for stall generation with configurable seed.
//
// Parameters:
//   MAX_STALL_CYCLES - Maximum consecutive stall cycles (0-3)
//   SEED - Random seed for reproducible stall patterns
//
// Stall behavior:
//   - On each new memory access (read or write), generates random stall duration
//   - Holds dmem_stall high for the selected duration
//   - Memory data is valid when stall goes low
//
module svc_rv_stall_injector #(
    parameter int MAX_STALL_CYCLES = 2,
    parameter int SEED             = 32'hACE1
) (
    input logic clk,
    input logic rst_n,

    //
    // CPU-side interface (directly from svc_rv)
    //
    input  logic        cpu_dmem_ren,
    input  logic [31:0] cpu_dmem_raddr,
    output logic [31:0] cpu_dmem_rdata,

    input logic        cpu_dmem_we,
    input logic [31:0] cpu_dmem_waddr,
    input logic [31:0] cpu_dmem_wdata,
    input logic [ 3:0] cpu_dmem_wstrb,

    output logic dmem_stall,

    //
    // Memory-side interface (to actual memory/IO)
    //
    output logic        mem_dmem_ren,
    output logic [31:0] mem_dmem_raddr,
    input  logic [31:0] mem_dmem_rdata,

    output logic        mem_dmem_we,
    output logic [31:0] mem_dmem_waddr,
    output logic [31:0] mem_dmem_wdata,
    output logic [ 3:0] mem_dmem_wstrb
);

  //
  // Initialize random seed
  //
  // verilator lint_off INITIALDLY
  integer seed_var;
  initial begin
    seed_var = SEED;
    seed_var = $urandom(seed_var);
  end
  // verilator lint_on INITIALDLY

  //
  // State machine
  //
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_STALLING,
    STATE_COMPLETE
  } state_t;

  state_t        state;
  state_t        state_next;

  //
  // Stall counter
  //
  logic   [ 1:0] stall_count;
  logic   [ 1:0] stall_count_next;
  logic   [ 1:0] stall_target;
  logic   [ 1:0] stall_target_next;

  //
  // Registered data for reads
  //
  logic   [31:0] rdata_reg;

  //
  // Detect new memory access
  //
  logic          new_access;
  assign new_access = (cpu_dmem_ren || cpu_dmem_we) && (state == STATE_IDLE);

  //
  // State machine
  //
  always_comb begin
    state_next        = state;
    stall_count_next  = stall_count;
    stall_target_next = stall_target;

    case (state)
      STATE_IDLE: begin
        if (new_access) begin
          stall_target_next = 2'($urandom_range(0, MAX_STALL_CYCLES));
          if (stall_target_next == 2'd0) begin
            // Stay in IDLE for zero-stall case to allow back-to-back accesses
            state_next = STATE_IDLE;
          end else begin
            state_next       = STATE_STALLING;
            stall_count_next = 2'd1;
          end
        end
      end

      STATE_STALLING: begin
        if (stall_count >= stall_target) begin
          state_next       = STATE_COMPLETE;
          stall_count_next = 2'd0;
        end else begin
          stall_count_next = stall_count + 1;
        end
      end

      STATE_COMPLETE: begin
        state_next = STATE_IDLE;
      end

      default: begin
        state_next = STATE_IDLE;
      end
    endcase
  end

  //
  // State registers
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state        <= STATE_IDLE;
      stall_count  <= 2'd0;
      stall_target <= 2'd0;
      rdata_reg    <= 32'd0;
    end else begin
      state        <= state_next;
      stall_count  <= stall_count_next;
      stall_target <= stall_target_next;

      // Capture read data when available
      if (state == STATE_STALLING || (state == STATE_IDLE && new_access)) begin
        rdata_reg <= mem_dmem_rdata;
      end
    end
  end

  //
  // Output assignments
  //
  // Stall is active during STALLING state
  assign dmem_stall =
      ((state == STATE_STALLING) ||
       (state == STATE_IDLE && new_access && stall_target_next != 2'd0));

  // Pass through addresses and write data
  assign mem_dmem_raddr = cpu_dmem_raddr;
  assign mem_dmem_waddr = cpu_dmem_waddr;
  assign mem_dmem_wdata = cpu_dmem_wdata;
  assign mem_dmem_wstrb = cpu_dmem_wstrb;

  // Memory operations occur on the first cycle
  assign mem_dmem_ren = cpu_dmem_ren && (state == STATE_IDLE);
  assign mem_dmem_we = cpu_dmem_we && (state == STATE_IDLE);

  // Read data: use registered value during/after stall, direct otherwise
  assign cpu_dmem_rdata = ((state == STATE_IDLE && !dmem_stall) ?
                           mem_dmem_rdata : rdata_reg);

endmodule

`endif
