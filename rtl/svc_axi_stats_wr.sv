`ifndef SVC_AXI_STATS_WR_SV
`define SVC_AXI_STATS_WR_SV

`include "svc.sv"
`include "svc_stats_cnt.sv"
`include "svc_stats_max.sv"
`include "svc_stats_val.sv"

// TODO: error detection in the stat modules.
// Use it at the bottom for stat_err.

// TODO: return the stats

// This uses the same bucketing described in:
//
//   https://zipcpu.com/blog/2021/08/14/axiperf.html
//
// His taxonomy is a good one, and aligns with the svc design goals
// of focusing on througput.

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_stats_wr #(
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter STAT_WIDTH     = 32
) (
    input logic clk,
    input logic rst_n,

    input  logic stat_clear,
    output logic stat_err,

    // If we get a soft core running, this should change to be memory mapped
    // via an axi register interface, but for now, this is easy. It also
    // let's us add new stats without having to change code anyplace else,
    // other than the final (off fpga) consumer.
    input  logic                  stat_iter_start,
    output logic                  stat_iter_valid,
    output logic [           7:0] stat_iter_id,
    output logic [STAT_WIDTH-1:0] stat_iter_val,
    output logic                  stat_iter_last,
    input  logic                  stat_iter_ready,

    input logic                      m_axi_awvalid,
    input logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    input logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    input logic [               7:0] m_axi_awlen,
    input logic [               2:0] m_axi_awsize,
    input logic [               1:0] m_axi_awburst,
    input logic                      m_axi_awready,
    input logic                      m_axi_wvalid,
    input logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    input logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    input logic                      m_axi_wlast,
    input logic                      m_axi_wready,
    input logic                      m_axi_bvalid,
    input logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input logic [               1:0] m_axi_bresp,
    input logic                      m_axi_bready
);
  localparam SW = STAT_WIDTH;
  localparam ASW = AXI_STRB_WIDTH;

  typedef enum {
    STATE_IDLE,
    STATE_ITER
  } state_t;

  typedef enum logic [7:0] {
    STAT_AW_BURST_CNT      = 0,
    STAT_AW_DEPTH_MAX      = 1,
    STAT_AW_LEN_MIN        = 2,
    STAT_AW_LEN_MAX        = 3,
    STAT_AW_BYTES_SUM      = 4,
    STAT_AW_BYTES_MIN      = 5,
    STAT_AW_BYTES_MAX      = 6,
    STAT_W_BURST_CNT       = 7,
    STAT_W_DEPTH_MAX       = 8,
    STAT_W_BEAT_CNT        = 9,
    STAT_W_BYTES_SUM       = 10,
    STAT_W_BYTES_MIN       = 11,
    STAT_W_BYTES_MAX       = 12,
    STAT_W_DATA_LAG_CNT    = 13,
    STAT_W_IDLE_CNT        = 14,
    STAT_W_EARLY_BEAT_CNT  = 15,
    STAT_W_AWR_EARLY_CNT   = 16,
    STAT_W_B_LAG_CNT       = 17,
    STAT_W_B_STALL_CNT     = 18,
    STAT_W_B_END_CNT       = 19,
    STAT_W_SLOW_DATA_CNT   = 20,
    STAT_W_STALL_CNT       = 21,
    STAT_W_ADDR_STALL_CNT  = 22,
    STAT_W_ADDR_LAG_CNT    = 23,
    STAT_W_EARLY_STALL_CNT = 24
  } stat_id_t;

  state_t           state;
  state_t           state_next;

  // not part of the state machine to make it easy to add new ones
  logic   [    7:0] iter_idx;
  logic   [    7:0] iter_idx_next;

  logic             stat_iter_valid_next;
  logic   [    7:0] stat_iter_id_next;
  logic   [ SW-1:0] stat_iter_val_next;
  logic             stat_iter_last_next;

  logic   [    7:0] aw_outstanding_cnt;
  logic   [    7:0] aw_outstanding_max;

  logic   [    7:0] w_outstanding_cnt;
  logic   [    7:0] w_outstanding_max;

  logic             w_in_progress;

  logic   [ SW-1:0] aw_burst_cnt;
  logic   [ SW-1:0] w_burst_cnt;

  logic   [ SW-1:0] w_beat_cnt;

  logic   [    7:0] awlen_min;
  logic   [    7:0] awlen_max;

  logic   [ SW-1:0] aw_bytes_min;
  logic   [ SW-1:0] aw_bytes_max;
  logic   [ SW-1:0] aw_bytes_sum;

  logic   [ASW-1:0] w_bytes;
  logic   [ASW-1:0] w_bytes_min;
  logic   [ASW-1:0] w_bytes_max;
  logic   [ SW-1:0] w_bytes_sum;

  // the cycle counters. see the zipcpu blog post
  logic   [ SW-1:0] w_data_lag_cnt;
  logic   [ SW-1:0] w_idle_cycles_cnt;
  logic   [ SW-1:0] w_early_beat_cnt;
  logic   [ SW-1:0] w_awr_early_cnt;
  logic   [ SW-1:0] w_b_lag_count_cnt;
  logic   [ SW-1:0] w_b_stall_count_cnt;
  logic   [ SW-1:0] w_b_end_count_cnt;
  logic   [ SW-1:0] w_slow_data_cnt;
  logic   [ SW-1:0] w_stall_cnt;
  logic   [ SW-1:0] w_addr_stall_cnt;
  logic   [ SW-1:0] w_addr_lag_cnt;
  logic   [ SW-1:0] w_early_stall_cnt;

  logic             w_data_lag_cnt_en;
  logic             w_idle_cycles_cnt_en;
  logic             w_early_beat_cnt_en;
  logic             w_awr_early_cnt_en;
  logic             w_b_lag_count_cnt_en;
  logic             w_b_stall_count_cnt_en;
  logic             w_b_end_count_cnt_en;
  logic             w_slow_data_cnt_en;
  logic             w_stall_cnt_en;
  logic             w_addr_stall_cnt_en;
  logic             w_addr_lag_cnt_en;
  logic             w_early_stall_cnt_en;


  always_comb begin
    state_next           = state;
    iter_idx_next        = iter_idx;

    stat_iter_valid_next = stat_iter_valid && !stat_iter_ready;
    stat_iter_id_next    = stat_iter_id;
    stat_iter_val_next   = stat_iter_val;
    stat_iter_last_next  = stat_iter_last;

    case (state)
      STATE_IDLE: begin
        if (stat_iter_start) begin
          state_next          = STATE_ITER;
          iter_idx_next       = 0;
          stat_iter_last_next = 1'b0;
        end
      end

      STATE_ITER: begin
        if (!stat_iter_valid || stat_iter_ready) begin
          stat_iter_valid_next = 1'b1;
          stat_iter_id_next    = iter_idx;
          iter_idx_next        = iter_idx_next + 1;

          case (iter_idx)
            STAT_AW_BURST_CNT: begin
              stat_iter_val_next = aw_burst_cnt;
            end

            STAT_AW_DEPTH_MAX: begin
              stat_iter_val_next = STAT_WIDTH'(aw_outstanding_max);
            end

            STAT_AW_LEN_MIN: begin
              stat_iter_val_next = STAT_WIDTH'(awlen_min);
            end

            STAT_AW_LEN_MAX: begin
              stat_iter_val_next = STAT_WIDTH'(awlen_max);
            end

            STAT_AW_BYTES_SUM: begin
              stat_iter_val_next = aw_bytes_sum;
            end

            STAT_AW_BYTES_MIN: begin
              stat_iter_val_next = aw_bytes_min;
            end

            STAT_AW_BYTES_MAX: begin
              stat_iter_val_next = aw_bytes_max;
            end

            STAT_W_BURST_CNT: begin
              stat_iter_val_next = w_burst_cnt;
            end

            STAT_W_DEPTH_MAX: begin
              stat_iter_val_next = STAT_WIDTH'(w_outstanding_max);
            end

            STAT_W_BEAT_CNT: begin
              stat_iter_val_next = w_beat_cnt;
            end

            STAT_W_BYTES_SUM: begin
              stat_iter_val_next = w_bytes_sum;
            end

            STAT_W_BYTES_MIN: begin
              stat_iter_val_next = STAT_WIDTH'(w_bytes_min);
            end

            STAT_W_BYTES_MAX: begin
              stat_iter_val_next = STAT_WIDTH'(w_bytes_max);
            end

            STAT_W_DATA_LAG_CNT: begin
              stat_iter_val_next = w_data_lag_cnt;
            end

            STAT_W_IDLE_CNT: begin
              stat_iter_val_next = w_idle_cycles_cnt;
            end

            STAT_W_EARLY_BEAT_CNT: begin
              stat_iter_val_next = w_early_beat_cnt;
            end

            STAT_W_AWR_EARLY_CNT: begin
              stat_iter_val_next = w_awr_early_cnt;
            end

            STAT_W_B_LAG_CNT: begin
              stat_iter_val_next = w_b_lag_count_cnt;
            end

            STAT_W_B_STALL_CNT: begin
              stat_iter_val_next = w_b_stall_count_cnt;
            end

            STAT_W_B_END_CNT: begin
              stat_iter_val_next = w_b_end_count_cnt;
            end

            STAT_W_SLOW_DATA_CNT: begin
              stat_iter_val_next = w_slow_data_cnt;
            end

            STAT_W_STALL_CNT: begin
              stat_iter_val_next = w_stall_cnt;
            end

            STAT_W_ADDR_STALL_CNT: begin
              stat_iter_val_next = w_addr_stall_cnt;
            end

            STAT_W_ADDR_LAG_CNT: begin
              stat_iter_val_next = w_addr_lag_cnt;
            end

            STAT_W_EARLY_STALL_CNT: begin
              stat_iter_val_next  = w_early_stall_cnt;
              stat_iter_last_next = 1'b1;
              state_next          = STATE_IDLE;
            end

            default: begin
              stat_iter_id_next  = '0;
              stat_iter_val_next = '0;
            end
          endcase
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state           <= STATE_IDLE;
      stat_iter_valid <= 1'b0;
    end else begin
      state           <= state_next;
      stat_iter_valid <= stat_iter_valid_next;
    end
  end

  always_ff @(posedge clk) begin
    iter_idx       <= iter_idx_next;
    stat_iter_id   <= stat_iter_id_next;
    stat_iter_val  <= stat_iter_val_next;
    stat_iter_last <= stat_iter_last_next;
  end

  // aw bursts
  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_aw_burst (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_awvalid && m_axi_awready),
      .dec  (1'b0),
      .cnt  (aw_burst_cnt)
  );

  // awlen
  svc_stats_val #(
      .WIDTH(8)
  ) svc_stats_val_awlen (
      .clk  (clk),
      .rst_n(rst_n),

      .clr(stat_clear),
      .en (m_axi_awvalid && m_axi_awready),
      .val(m_axi_awlen),
      .min(awlen_min),
      .max(awlen_max),
      .sum()
  );

  // aw_bytes
  svc_stats_val #(
      .WIDTH     (STAT_WIDTH),
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_val_aw_bytes (
      .clk  (clk),
      .rst_n(rst_n),

      .clr(stat_clear),
      .en (m_axi_awvalid && m_axi_awready),
      .val((STAT_WIDTH'(m_axi_awlen) + 1) << m_axi_awsize),
      .min(aw_bytes_min),
      .max(aw_bytes_max),
      .sum(aw_bytes_sum)
  );

  // w bursts
  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_burst (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .dec  (1'b0),
      .cnt  (w_burst_cnt)
  );

  // w beats
  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_beat (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_wvalid && m_axi_wready),
      .dec  (1'b0),
      .cnt  (w_beat_cnt)
  );

  always_comb begin
    w_bytes = 0;
    for (int i = 0; i < AXI_STRB_WIDTH; i = i + 1) begin
      w_bytes = w_bytes + m_axi_wstrb[i];
    end
  end

  // w_bytes
  svc_stats_val #(
      .WIDTH     (AXI_STRB_WIDTH),
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_val_w_bytes (
      .clk  (clk),
      .rst_n(rst_n),

      .clr(stat_clear),
      .en (m_axi_wvalid && m_axi_wready),
      .val(w_bytes),
      .min(w_bytes_min),
      .max(w_bytes_max),
      .sum(w_bytes_sum)
  );

  // The AW and W outstanding might seem like odd definitions. Why not
  // consider W outstanding to be from m_axi_wvalid going high,
  // for example? These are used to bucket clocks into categories.
  // Look to the casez below, but, there there is a good writeup
  // about these categories and how these 2 vals are used on the
  // zipcpu blog link above.
  //
  // NOTE: AW and W outstanding stats must currently be immediate.
  // If extra stat stages are used by the accumulator, the values
  // will be out of sync with the axi signals in the casez below.
  // If more pipelining is ever needed for these, the axi signals
  // will need to be delayed to match.

  // aw outstanding (aw txn accept to b txn accept)
  svc_stats_cnt #(
      .STAT_WIDTH(8),
      .STAGES    (0)
  ) svc_stats_cnt_aw_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_awvalid && m_axi_awready),
      .dec  (m_axi_bvalid && m_axi_bready),
      .cnt  (aw_outstanding_cnt)
  );

  svc_stats_max #(
      .WIDTH(8)
  ) svc_stats_max_aw_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .en   (1'b1),
      .val  (aw_outstanding_cnt),
      .max  (aw_outstanding_max)
  );

  // w outstanding (last w txn accept to b txn accept)
  svc_stats_cnt #(
      .STAT_WIDTH(8),
      .STAGES    (0)
  ) svc_stats_cnt_w_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .dec  (m_axi_bvalid && m_axi_bready),
      .cnt  (w_outstanding_cnt)
  );

  svc_stats_max #(
      .WIDTH(8)
  ) svc_stats_max_w_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .en   (1'b1),
      .val  (w_outstanding_cnt),
      .max  (w_outstanding_max)
  );

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      w_in_progress <= 1'b0;
    end else begin
      if (m_axi_wvalid) begin
        w_in_progress <= !(m_axi_wready && m_axi_wlast);
      end
    end
  end

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_data_lag (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_data_lag_cnt_en),
      .dec  (1'b0),
      .cnt  (w_data_lag_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_idle_cycles (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_idle_cycles_cnt_en),
      .dec  (1'b0),
      .cnt  (w_idle_cycles_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_early_beat (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_early_beat_cnt_en),
      .dec  (1'b0),
      .cnt  (w_early_beat_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_awr_early (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_awr_early_cnt_en),
      .dec  (1'b0),
      .cnt  (w_awr_early_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_b_lag_count (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_b_lag_count_cnt_en),
      .dec  (1'b0),
      .cnt  (w_b_lag_count_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_b_stall_count (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_b_stall_count_cnt_en),
      .dec  (1'b0),
      .cnt  (w_b_stall_count_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_b_end_count (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_b_end_count_cnt_en),
      .dec  (1'b0),
      .cnt  (w_b_end_count_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_slow_data (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_slow_data_cnt_en),
      .dec  (1'b0),
      .cnt  (w_slow_data_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_stall (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_stall_cnt_en),
      .dec  (1'b0),
      .cnt  (w_stall_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_addr_stall (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_addr_stall_cnt_en),
      .dec  (1'b0),
      .cnt  (w_addr_stall_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_addr_lag (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_addr_lag_cnt_en),
      .dec  (1'b0),
      .cnt  (w_addr_lag_cnt)
  );

  svc_stats_cnt #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_cnt_w_early_stall (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (w_early_stall_cnt_en),
      .dec  (1'b0),
      .cnt  (w_early_stall_cnt)
  );

  // see the zipcpu blog to better understand these bins
  always_ff @(posedge clk)
    if (!rst_n || stat_clear) begin
    end else begin
      w_idle_cycles_cnt_en   <= 1'b0;
      w_slow_data_cnt_en     <= 1'b0;
      w_stall_cnt_en         <= 1'b0;
      w_stall_cnt_en         <= 1'b0;
      w_early_beat_cnt_en    <= 1'b0;
      w_awr_early_cnt_en     <= 1'b0;
      w_addr_stall_cnt_en    <= 1'b0;
      w_data_lag_cnt_en      <= 1'b0;
      w_addr_lag_cnt_en      <= 1'b0;
      w_addr_lag_cnt_en      <= 1'b0;
      w_early_stall_cnt_en   <= 1'b0;
      w_b_lag_count_cnt_en   <= 1'b0;
      w_b_stall_count_cnt_en <= 1'b0;
      w_b_end_count_cnt_en   <= 1'b0;
      casez ({
        aw_outstanding_cnt != 0,
        w_outstanding_cnt != 0,
        w_in_progress,
        m_axi_awvalid,
        m_axi_awready,
        m_axi_wvalid,
        m_axi_wready,
        m_axi_bvalid,
        m_axi_bready
      })
        //
        // Idle
        //
        9'b0000?0???: w_idle_cycles_cnt_en <= 1'b1;

        //
        // Throughput
        //
        9'b1?1??0???: w_slow_data_cnt_en <= 1'b1;
        9'b1????10??: w_stall_cnt_en <= 1'b1;
        9'b0?1??10??: w_stall_cnt_en <= 1'b1;
        9'b0??0?11??: w_early_beat_cnt_en <= 1'b1;

        //
        // Latency
        //
        9'b000110???: w_awr_early_cnt_en <= 1'b1;
        9'b000100???: w_addr_stall_cnt_en <= 1'b1;

        9'b100??0???: w_data_lag_cnt_en <= 1'b1;
        9'b010??0???: w_addr_lag_cnt_en <= 1'b1;
        9'b0?1??0???: w_addr_lag_cnt_en <= 1'b1;
        9'b0?0??10??: w_early_stall_cnt_en <= 1'b1;

        9'b110??0?0?: w_b_lag_count_cnt_en <= 1'b1;
        9'b110??0?10: w_b_stall_count_cnt_en <= 1'b1;
        9'b110??0?11: w_b_end_count_cnt_en <= 1'b1;

        default: begin
        end
      endcase
    end

  assign stat_err = 1'b0;

endmodule
`endif
