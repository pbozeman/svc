`ifndef SVC_AXI_STATS_WR_SV
`define SVC_AXI_STATS_WR_SV

`include "svc.sv"
`include "svc_stats_counter.sv"
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
// verilator lint_off: UNUSEDPARAM
module svc_axi_stats_wr #(
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter STAT_WIDTH     = 32
    // parameter STAT_ADDR_WIDTH = 3
) (
    input logic clk,
    input logic rst_n,

    input  logic stat_clear,
    output logic stat_err,

    output logic [SW-1:0] stat_aw_burst_cnt,

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

  logic [ SW-1:0] aw_outstanding_cnt;
  logic [ SW-1:0] aw_outstanding_max;

  logic [ SW-1:0] w_outstanding_cnt;
  logic [ SW-1:0] w_outstanding_max;

  logic           w_in_progress;

  logic [ SW-1:0] aw_burst_cnt;
  logic [ SW-1:0] w_burst_cnt;

  logic [ SW-1:0] w_beat_cnt;

  logic [    7:0] awlen_min;
  logic [    7:0] awlen_max;

  logic [ SW-1:0] aw_bytes_min;
  logic [ SW-1:0] aw_bytes_max;
  logic [ SW-1:0] aw_bytes_sum;

  logic [ASW-1:0] w_bytes;
  logic [ASW-1:0] w_bytes_min;
  logic [ASW-1:0] w_bytes_max;
  logic [ SW-1:0] w_bytes_sum;

  // the cycle counters. see the zipcpu blog post
  logic [ SW-1:0] w_data_lag_cnt;
  logic [ SW-1:0] w_idle_cycles_cnt;
  logic [ SW-1:0] w_early_beat_cnt;
  logic [ SW-1:0] w_awr_early_cnt;
  logic [ SW-1:0] w_b_lag_count_cnt;
  logic [ SW-1:0] w_b_stall_count_cnt;
  logic [ SW-1:0] w_b_end_count_cnt;
  logic [ SW-1:0] w_slow_data_cnt;
  logic [ SW-1:0] w_stall_cnt;
  logic [ SW-1:0] w_addr_stall_cnt;
  logic [ SW-1:0] w_addr_lag_cnt;
  logic [ SW-1:0] w_early_stall_cnt;

  assign stat_aw_burst_cnt = aw_burst_cnt;

  // aw bursts
  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_counter_aw_burst (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (m_axi_awvalid && m_axi_awready),
      .stat_dec  (1'b0),
      .stat_cnt  (aw_burst_cnt),
      .stat_max  ()
  );

  // awlen
  svc_stats_val #(
      .WIDTH     (8),
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_val_awlen (
      .clk  (clk),
      .rst_n(rst_n),

      .stat_clear(stat_clear),
      .stat_en   (m_axi_awvalid && m_axi_awready),
      .stat_val  (m_axi_awlen),
      .stat_min  (awlen_min),
      .stat_max  (awlen_max),
      .stat_sum  ()
  );

  // aw_bytes
  svc_stats_val #(
      .WIDTH     (STAT_WIDTH),
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_val_aw_bytes (
      .clk  (clk),
      .rst_n(rst_n),

      .stat_clear(stat_clear),
      .stat_en   (m_axi_awvalid && m_axi_awready),
      .stat_val  ((STAT_WIDTH'(m_axi_awlen) + 1) << m_axi_awsize),
      .stat_min  (aw_bytes_min),
      .stat_max  (aw_bytes_max),
      .stat_sum  (aw_bytes_sum)
  );

  // w bursts
  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_counter_w_burst (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .stat_dec  (1'b0),
      .stat_cnt  (w_burst_cnt),
      .stat_max  ()
  );

  // w beats
  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_counter_w_beat (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (m_axi_wvalid && m_axi_wready),
      .stat_dec  (1'b0),
      .stat_cnt  (w_beat_cnt),
      .stat_max  ()
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

      .stat_clear(stat_clear),
      .stat_en   (m_axi_wvalid && m_axi_wready),
      .stat_val  (w_bytes),
      .stat_min  (w_bytes_min),
      .stat_max  (w_bytes_max),
      .stat_sum  (w_bytes_sum)
  );

  // The AW and W outstanding might seem like odd definitions. Why not
  // consider W outstanding to be from m_axi_wvalid going high,
  // for example? These are used to bucket clocks into categories.
  // Look to the casez below, but, there there is a good writeup
  // about these categories and how these 2 vals are used on the
  // zipcpu blog link above.

  // aw outstanding (aw txn accept to b txn accept)
  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_counter_aw_outstanding (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (m_axi_awvalid && m_axi_awready),
      .stat_dec  (m_axi_bvalid && m_axi_bready),
      .stat_cnt  (aw_outstanding_cnt),
      .stat_max  (aw_outstanding_max)
  );

  // w outstanding (last w txn accept to b txn accept)
  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) svc_stats_counter_w_outstanding (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .stat_dec  (m_axi_bvalid && m_axi_bready),
      .stat_cnt  (w_outstanding_cnt),
      .stat_max  (w_outstanding_max)
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

  // see the zipcpu blog to better understand these bins
  // (and yes, this part was pretty much a direct copy with renames)
  always_ff @(posedge clk)
    if (!rst_n || stat_clear) begin
      w_data_lag_cnt      <= 0;
      w_idle_cycles_cnt   <= 0;
      w_early_beat_cnt    <= 0;
      w_awr_early_cnt     <= 0;
      w_b_lag_count_cnt   <= 0;
      w_b_stall_count_cnt <= 0;
      w_b_end_count_cnt   <= 0;
      w_slow_data_cnt     <= 0;
      w_stall_cnt         <= 0;
      w_data_lag_cnt      <= 0;
      w_addr_stall_cnt    <= 0;
      w_addr_lag_cnt      <= 0;
      w_early_stall_cnt   <= 0;
    end else begin
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
        9'b0000?0???: w_idle_cycles_cnt <= w_idle_cycles_cnt + 1;

        //
        // Throughput
        //
        9'b1?1??0???: w_slow_data_cnt <= w_slow_data_cnt + 1;
        9'b1????10??: w_stall_cnt <= w_stall_cnt + 1;
        9'b0?1??10??: w_stall_cnt <= w_stall_cnt + 1;
        9'b0??0?11??: w_early_beat_cnt <= w_early_beat_cnt + 1;

        //
        // Latency
        //
        9'b000110???: w_awr_early_cnt <= w_awr_early_cnt + 1;
        9'b000100???: w_addr_stall_cnt <= w_addr_stall_cnt + 1;

        9'b100??0???: w_data_lag_cnt <= w_data_lag_cnt + 1;
        9'b010??0???: w_addr_lag_cnt <= w_addr_lag_cnt + 1;
        9'b0?1??0???: w_addr_lag_cnt <= w_addr_lag_cnt + 1;
        9'b0?0??10??: w_early_stall_cnt <= w_early_stall_cnt + 1;

        9'b110??0?0?: w_b_lag_count_cnt <= w_b_lag_count_cnt + 1;
        9'b110??0?10: w_b_stall_count_cnt <= w_b_stall_count_cnt + 1;
        9'b110??0?11: w_b_end_count_cnt <= w_b_end_count_cnt + 1;

        default: begin
        end
      endcase
    end

  assign stat_err = 1'b0;

endmodule
`endif
