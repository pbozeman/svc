`ifndef SVC_STATS_TIMER_SV
`define SVC_STATS_TIMER_SV

`include "svc.sv"

// stats timer with cnt/min/max
//
// Circular buffers are used to track start/end times. If they overflow,
// older entries are discarded in favor of keeping the newer ones.
//
// The original thinking was if the depth was large, and drops are infrequent,
// we would want fresh data. But, the tb was a pain, and this might result
// in never having stats. This might be worth revisiting and dropping
// start events. Wait and see how this plays out in real usage.
//
// Average was left out because its a bit of a pain with 32 bit counters.
// The total time would overflow after about 42 seconds on the ice40 at 100mhz,
// and would be worse at with better chips and higher clock rates. Plus, avg
// is somewhat useless compared percentiles. If needed, expose the 2 queues and
// let a caller compute them, or other stats. For now, just do the simple
// thing.

// verilator lint_off: UNUSEDSIGNAL
module svc_stats_timer #(
    parameter ADDR_WIDTH = 3,
    parameter STAT_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,

    input logic stat_clear,
    input logic stat_start,
    input logic stat_end,

    output logic [STAT_WIDTH-1:0] drop_cnt,

    output logic [STAT_WIDTH-1:0] stat_min,
    output logic [STAT_WIDTH-1:0] stat_max,
    output logic [STAT_WIDTH-1:0] stat_sum,

    output logic [STAT_WIDTH-1:0] stat_cnt
);
  localparam AW = ADDR_WIDTH;
  localparam SW = STAT_WIDTH;
  localparam DEPTH = 1 << ADDR_WIDTH;

  logic [SW-1:0] clk_cnt;

  logic [SW-1:0] clk_start     [DEPTH];
  logic [SW-1:0] clk_end       [DEPTH];

  logic [AW-1:0] start_idx;
  logic [AW-1:0] end_idx;

  logic [SW-1:0] outstanding;

  logic [SW-1:0] elapsed;
  logic          elapsed_valid;

  //
  // clock counter
  //
  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      clk_cnt <= 0;
    end else begin
      clk_cnt <= clk_cnt + 1;
    end
  end

  //
  // dropped event counter
  //
  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      drop_cnt <= 0;
    end else begin
      if (stat_start && (outstanding >= DEPTH)) begin
        drop_cnt <= drop_cnt + 1;
      end
    end
  end

  //
  // record start
  //
  always @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      start_idx <= 0;
      for (int i = 0; i < DEPTH; i++) begin
        clk_start[i] <= 0;
      end
    end else begin
      if (stat_start) begin
        start_idx            <= start_idx + 1;
        clk_start[start_idx] <= clk_cnt;
      end
    end
  end

  //
  // record end and capture time measurement
  //
  always @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      end_idx <= 0;
      for (int i = 0; i < DEPTH; i++) begin
        clk_end[i] <= 0;
      end
      elapsed       <= 0;
      elapsed_valid <= 1'b0;
    end else begin
      elapsed_valid <= 1'b0;
      if (stat_end) begin
        clk_end[end_idx] <= clk_cnt;
        end_idx          <= end_idx + 1;
        elapsed          <= clk_cnt - clk_start[end_idx];
        elapsed_valid    <= 1'b1;
      end
    end
  end

  //
  // outstanding
  //
  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      outstanding <= 0;
    end else begin
      case ({
        stat_end, stat_start
      })
        2'b00: begin
          // neither, so no change
        end

        2'b01: begin
          outstanding <= outstanding + 1;
        end

        2'b10: begin
          outstanding <= outstanding - 1;
        end

        2'b11: begin
          // both, so no net change
        end
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      stat_cnt <= 0;
      stat_sum <= 0;
      stat_min <= '1;
      stat_max <= 0;
    end else begin
      if (elapsed_valid) begin
        stat_cnt <= stat_cnt + 1;
        stat_sum <= stat_sum + elapsed;

        // Update min/max
        if (elapsed < stat_min) begin
          stat_min <= elapsed;
        end
        if (elapsed > stat_max) begin
          stat_max <= elapsed;
        end
      end
    end
  end

endmodule
`endif
