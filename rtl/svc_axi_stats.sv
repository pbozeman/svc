`ifndef SVC_AXI_STATS_SV
`define SVC_AXI_STATS_SV

`include "svc.sv"
`include "svc_axil_regfile.sv"
`include "svc_stats_cnt.sv"
`include "svc_stats_max.sv"
`include "svc_stats_val.sv"
`include "svc_unused.sv"

// This uses the same bucketing described in:
//
//   https://zipcpu.com/blog/2021/08/14/axiperf.html
//
// His taxonomy is a good one, and aligns with the svc design goals
// of focusing on throughput. The implementation is fairly different.
//
// I'd prefer to separate the rd/wr into separate modules, but that complicates
// the csr implementation. There would need to be a router up above, 2 sets of
// signals for the main router, or the stats would all need to get passed out
// and then put behind a csr. That final option might be the cleanest, but
// this is fine for now.

module svc_axi_stats #(
    parameter STAT_WIDTH      = 32,
    parameter AXIL_ADDR_WIDTH = 8,
    parameter AXIL_DATA_WIDTH = STAT_WIDTH,
    parameter AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8,
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXI_STRB_WIDTH  = AXI_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input  logic stat_clear,
    output logic stat_err,

    // register interface for stat reporting
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic                       s_axil_bvalid,
    output logic [                1:0] s_axil_bresp,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic                       s_axil_rvalid,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    input  logic                       s_axil_rready,

    // axi interface to monitor and collect stats on
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
    input logic                      m_axi_bready,

    input logic                      m_axi_arvalid,
    input logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    input logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    input logic [               7:0] m_axi_arlen,
    input logic [               2:0] m_axi_arsize,
    input logic [               1:0] m_axi_arburst,
    input logic                      m_axi_arready,
    input logic                      m_axi_rvalid,
    input logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input logic [               1:0] m_axi_rresp,
    input logic                      m_axi_rlast,
    input logic                      m_axi_rready
);
  localparam NUM_R = 45;

  // Register IDs
  typedef enum {
    REG_AW_BURST_CNT       = 0,
    REG_AW_DEPTH_MAX       = 1,
    REG_AW_LEN_MIN         = 2,
    REG_AW_LEN_MAX         = 3,
    REG_AW_BYTES_SUM       = 4,
    REG_AW_BYTES_MIN       = 5,
    REG_AW_BYTES_MAX       = 6,
    REG_W_BURST_CNT        = 7,
    REG_W_DEPTH_MAX        = 8,
    REG_W_BEAT_CNT         = 9,
    REG_W_BYTES_SUM        = 10,
    REG_W_BYTES_MIN        = 11,
    REG_W_BYTES_MAX        = 12,
    REG_W_DATA_LAG_CNT     = 13,
    REG_W_IDLE_CNT         = 14,
    REG_W_EARLY_BEAT_CNT   = 15,
    REG_W_AWR_EARLY_CNT    = 16,
    REG_W_B_LAG_CNT        = 17,
    REG_W_B_STALL_CNT      = 18,
    REG_W_B_END_CNT        = 19,
    REG_W_SLOW_DATA_CNT    = 20,
    REG_W_STALL_CNT        = 21,
    REG_W_ADDR_STALL_CNT   = 22,
    REG_W_ADDR_LAG_CNT     = 23,
    REG_W_EARLY_STALL_CNT  = 24,
    REG_W_ERR_CNT          = 25,
    REG_AR_BURST_CNT       = 26,
    REG_AR_DEPTH_MAX       = 27,
    REG_AR_LEN_MIN         = 28,
    REG_AR_LEN_MAX         = 29,
    REG_AR_BYTES_SUM       = 30,
    REG_AR_BYTES_MIN       = 31,
    REG_AR_BYTES_MAX       = 32,
    REG_R_BURST_CNT        = 33,
    REG_R_DEPTH_MAX        = 34,
    REG_R_BEAT_CNT         = 35,
    REG_RD_OUTSTANDING_MAX = 36,
    REG_RD_MAX_RESP        = 37,
    REG_RD_R_STALLS        = 38,
    REG_RD_SLOW_LINK       = 39,
    REG_RD_LAG             = 40,
    REG_RD_IDLE_CYCLES     = 41,
    REG_RD_AR_STALLS       = 42,
    REG_RD_AR_CYCLES       = 43,
    REG_R_ERR_CNT          = 44
  } reg_id_t;

  localparam SW = STAT_WIDTH;
  localparam ASW = AXI_STRB_WIDTH;

  //--------------------------------------------------------------------------
  //
  // Write stats declarations
  //
  //--------------------------------------------------------------------------

  // convert write strobe to bytes written
  logic [ASW-1:0] w_bytes;
  always_comb begin
    w_bytes = 0;
    for (int i = 0; i < AXI_STRB_WIDTH; i = i + 1) begin
      w_bytes = w_bytes + m_axi_wstrb[i];
    end
  end

  `SVC_STAT_CNT(SW, aw_burst_cnt, m_axi_awvalid && m_axi_awready);
  `SVC_STAT_CNT(SW, w_burst_cnt, m_axi_wvalid && m_axi_wready && m_axi_wlast);
  `SVC_STAT_CNT(SW, w_beat_cnt, m_axi_wvalid && m_axi_wready);
  `SVC_STAT_CNT(SW, w_err_cnt,
                m_axi_bvalid && m_axi_bready && m_axi_bresp != 2'b00);

  `SVC_STAT_MIN_MAX(8, awlen, m_axi_awlen, m_axi_awvalid && m_axi_awready);
  `SVC_STAT_VAL(SW, SW, aw_bytes, (SW'(m_axi_awlen) + 1) << m_axi_awsize,
                m_axi_awvalid && m_axi_awready);
  `SVC_STAT_VAL(SW, ASW, w_bytes, w_bytes, m_axi_wvalid && m_axi_wready);

  // the cycle counters. see the zipcpu blog post
  `SVC_STAT_CNT_EN(SW, w_data_lag_cnt);
  `SVC_STAT_CNT_EN(SW, w_idle_cycles_cnt);
  `SVC_STAT_CNT_EN(SW, w_early_beat_cnt);
  `SVC_STAT_CNT_EN(SW, w_awr_early_cnt);
  `SVC_STAT_CNT_EN(SW, w_b_lag_cnt);
  `SVC_STAT_CNT_EN(SW, w_b_stall_cnt);
  `SVC_STAT_CNT_EN(SW, w_slow_data_cnt);
  `SVC_STAT_CNT_EN(SW, w_b_end_cnt);
  `SVC_STAT_CNT_EN(SW, w_stall_cnt);
  `SVC_STAT_CNT_EN(SW, w_addr_stall_cnt);
  `SVC_STAT_CNT_EN(SW, w_addr_lag_cnt);
  `SVC_STAT_CNT_EN(SW, w_early_stall_cnt);

  //--------------------------------------------------------------------------
  //
  // Write stats collection
  //
  //--------------------------------------------------------------------------

  logic [7:0] aw_outstanding_cnt;
  logic [7:0] aw_outstanding_max;

  logic [7:0] w_outstanding_cnt;
  logic [7:0] w_outstanding_max;

  logic       w_in_progress;

  // The AW and W outstanding are special, internal stats.
  // They are used to bucket clocks into categories. Look to the casez below,
  // but, there there is a good writeup about these categories and how these
  // 2 vals are used on the zipcpu blog link above.
  //
  // NOTE: AW and W outstanding stats must currently be immediate.
  // If extra stat stages are used by the accumulator, the values
  // will be out of sync with the axi signals in the casez below.
  // If more pipelining is ever needed for these, the axi signals
  // will need to be delayed to match.
  //
  // Since they have special requirements, instantiate them directly
  // rather than using the macros.

  // aw outstanding (aw txn accept to b txn accept)
  svc_stats_cnt #(
      .STAT_WIDTH    (8),
      .BITS_PER_STAGE(8)
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
      .STAT_WIDTH    (8),
      .BITS_PER_STAGE(8)
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

  // see the zipcpu blog to better understand these bins
  always_ff @(posedge clk)
    if (rst_n || !stat_clear) begin
      w_idle_cycles_cnt_en <= 1'b0;
      w_slow_data_cnt_en   <= 1'b0;
      w_stall_cnt_en       <= 1'b0;
      w_stall_cnt_en       <= 1'b0;
      w_early_beat_cnt_en  <= 1'b0;
      w_awr_early_cnt_en   <= 1'b0;
      w_addr_stall_cnt_en  <= 1'b0;
      w_data_lag_cnt_en    <= 1'b0;
      w_addr_lag_cnt_en    <= 1'b0;
      w_addr_lag_cnt_en    <= 1'b0;
      w_early_stall_cnt_en <= 1'b0;
      w_b_lag_cnt_en       <= 1'b0;
      w_b_stall_cnt_en     <= 1'b0;
      w_b_end_cnt_en       <= 1'b0;
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

        9'b110??0?0?: w_b_lag_cnt_en <= 1'b1;
        9'b110??0?10: w_b_stall_cnt_en <= 1'b1;
        9'b110??0?11: w_b_end_cnt_en <= 1'b1;

        default: begin
        end
      endcase
    end

  //--------------------------------------------------------------------------
  //
  // Read stats declarations
  //
  //--------------------------------------------------------------------------
  localparam MAX_AXI_ID = 1 << AXI_ID_WIDTH;

  logic [             7:0] rd_outstanding_id    [0:MAX_AXI_ID-1];
  logic [  MAX_AXI_ID-1:0] rd_nz_outstanding_id;
  logic [  MAX_AXI_ID-1:0] rd_bursts_in_flight;

  logic [AXI_ID_WIDTH-1:0] rd_responding;
  logic [AXI_ID_WIDTH-1:0] rd_responding_next;

  logic [             7:0] rd_outstanding_cnt;
  logic [             7:0] rd_outstanding_max;

  `SVC_STAT_CNT(SW, ar_burst_cnt, m_axi_arvalid && m_axi_arready);
  `SVC_STAT_CNT(SW, r_burst_cnt, m_axi_rvalid && m_axi_rready && m_axi_rlast);
  `SVC_STAT_CNT(SW, r_beat_cnt, m_axi_rvalid && m_axi_rready);
  `SVC_STAT_CNT(SW, r_err_cnt,
                m_axi_rvalid && m_axi_rready && m_axi_rresp != 2'b00);

  `SVC_STAT_MIN_MAX(8, arlen, m_axi_arlen, m_axi_arvalid && m_axi_arready);
  `SVC_STAT_VAL(SW, SW, ar_bytes, (SW'(m_axi_arlen) + 1) << m_axi_arsize,
                m_axi_arvalid && m_axi_arready);

  `SVC_STAT_MAX(AXI_ID_WIDTH, rd_responding, rd_responding);
  `SVC_STAT_CNT(STAT_WIDTH, rd_r_stalls, m_axi_rvalid && !m_axi_rready);

  `SVC_STAT_CNT_EN(SW, rd_slow_link);
  `SVC_STAT_CNT_EN(SW, rd_lag);
  `SVC_STAT_CNT_EN(SW, rd_idle_cycles);
  `SVC_STAT_CNT_EN(SW, rd_ar_stalls);
  `SVC_STAT_CNT_EN(SW, rd_ar_cycles);


  //--------------------------------------------------------------------------
  //
  // Read stats collection
  //
  //--------------------------------------------------------------------------

  // rd outstanding (ar txn accept to r last txn accept)
  svc_stats_cnt #(
      .STAT_WIDTH    (8),
      .BITS_PER_STAGE(8)
  ) svc_stats_cnt_rd_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .inc  (m_axi_arvalid && m_axi_arready),
      .dec  (m_axi_rvalid && m_axi_rready && m_axi_rlast),
      .cnt  (rd_outstanding_cnt)
  );

  svc_stats_max #(
      .WIDTH(8)
  ) svc_stats_max_rd_outstanding (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .en   (1'b1),
      .val  (rd_outstanding_cnt),
      .max  (rd_outstanding_max)
  );

  for (genvar i = 0; i < (1 << AXI_ID_WIDTH); i++) begin : gen_rd_id_stats
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        rd_outstanding_id[i]    <= 0;
        rd_nz_outstanding_id[i] <= 0;
      end else begin
        case ({
          m_axi_arvalid && m_axi_arready && (m_axi_arid == i),
          m_axi_rvalid && m_axi_rready && m_axi_rlast && (m_axi_rid == i)
        })
          2'b10: begin
            rd_outstanding_id[i]    <= rd_outstanding_id[i] + 1;
            rd_nz_outstanding_id[i] <= 1'b1;
          end

          2'b01: begin
            rd_outstanding_id[i]    <= rd_outstanding_id[i] - 1;
            rd_nz_outstanding_id[i] <= (rd_outstanding_id[i] > 1);
          end

          default: begin
          end
        endcase
      end
    end

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        rd_bursts_in_flight[i] <= 0;
      end else begin
        if (m_axi_rvalid && m_axi_rid == i) begin
          rd_bursts_in_flight[i] <= !(m_axi_rready && m_axi_rlast);
        end
      end
    end
  end

  // not using always_comb because of an invalid warning from iverilog:
  // "warning: A for statement must use the index (i) in the condition
  // expression to be synthesized in an always_comb process." - which it is,
  // but this warning isn't issued with always @(*)
  always @(*) begin
    rd_responding_next = 0;
    for (int i = 0; i < MAX_AXI_ID; i++) begin
      if (rd_bursts_in_flight[i]) begin
        rd_responding_next = rd_responding_next + 1;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rd_responding <= 0;
    end else begin
      rd_responding <= rd_responding_next;
    end
  end

  always_ff @(posedge clk) begin
    if (rst_n || !stat_clear) begin
      rd_slow_link_en   <= 1'b0;
      rd_lag_en         <= 1'b0;
      rd_idle_cycles_en <= 1'b0;
      rd_ar_stalls_en   <= 1'b0;
      rd_ar_cycles_en   <= 1'b0;

      if (!m_axi_rvalid) begin
        if (rd_bursts_in_flight != 0) begin
          rd_slow_link_en <= 1'b1;
        end else if (rd_nz_outstanding_id != 0) begin
          rd_lag_en <= 1'b1;
        end else if (!m_axi_arvalid) begin
          rd_idle_cycles_en <= 1'b1;
        end else if (m_axi_arvalid && !m_axi_arready) begin
          rd_ar_stalls_en <= 1'b1;
        end else begin
          rd_ar_cycles_en <= 1'b1;
        end
      end
    end
  end

  //--------------------------------------------------------------------------
  //
  // Register file for stats interface (both read and write)
  //
  //--------------------------------------------------------------------------

  // all stats are read only, so no r_val_next
  logic [NUM_R-1:0][SW-1:0] r_val;

  svc_axil_regfile #(
      .N              (NUM_R),
      .DATA_WIDTH     (STAT_WIDTH),
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
      .REG_WRITE_MASK (0)
  ) svc_axil_regfile_i (
      .clk  (clk),
      .rst_n(rst_n),

      .r_val     (r_val),
      .r_val_next(),

      .s_axil_awaddr (s_axil_awaddr),
      .s_axil_awvalid(s_axil_awvalid),
      .s_axil_awready(s_axil_awready),
      .s_axil_wdata  (s_axil_wdata),
      .s_axil_wstrb  (s_axil_wstrb),
      .s_axil_wvalid (s_axil_wvalid),
      .s_axil_wready (s_axil_wready),
      .s_axil_bvalid (s_axil_bvalid),
      .s_axil_bresp  (s_axil_bresp),
      .s_axil_bready (s_axil_bready),

      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arready(s_axil_arready),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rready (s_axil_rready)
  );

  // FIXME: rd_outstanding_max should come from a non ar version,
  // like is done with writes
  always_comb begin
    r_val[REG_AW_BURST_CNT]       = SW'(aw_burst_cnt);
    r_val[REG_AW_DEPTH_MAX]       = SW'(aw_outstanding_max);
    r_val[REG_AW_LEN_MIN]         = SW'(awlen_min);
    r_val[REG_AW_LEN_MAX]         = SW'(awlen_max);
    r_val[REG_AW_BYTES_SUM]       = SW'(aw_bytes_sum);
    r_val[REG_AW_BYTES_MIN]       = SW'(aw_bytes_min);
    r_val[REG_AW_BYTES_MAX]       = SW'(aw_bytes_max);
    r_val[REG_W_BURST_CNT]        = SW'(w_burst_cnt);
    r_val[REG_W_DEPTH_MAX]        = SW'(w_outstanding_max);
    r_val[REG_W_BEAT_CNT]         = SW'(w_beat_cnt);
    r_val[REG_W_BYTES_SUM]        = SW'(w_bytes_sum);
    r_val[REG_W_BYTES_MIN]        = SW'(w_bytes_min);
    r_val[REG_W_BYTES_MAX]        = SW'(w_bytes_max);
    r_val[REG_W_DATA_LAG_CNT]     = SW'(w_data_lag_cnt);
    r_val[REG_W_IDLE_CNT]         = SW'(w_idle_cycles_cnt);
    r_val[REG_W_EARLY_BEAT_CNT]   = SW'(w_early_beat_cnt);
    r_val[REG_W_AWR_EARLY_CNT]    = SW'(w_awr_early_cnt);
    r_val[REG_W_B_LAG_CNT]        = SW'(w_b_lag_cnt);
    r_val[REG_W_B_STALL_CNT]      = SW'(w_b_stall_cnt);
    r_val[REG_W_B_END_CNT]        = SW'(w_b_end_cnt);
    r_val[REG_W_SLOW_DATA_CNT]    = SW'(w_slow_data_cnt);
    r_val[REG_W_STALL_CNT]        = SW'(w_stall_cnt);
    r_val[REG_W_ADDR_STALL_CNT]   = SW'(w_addr_stall_cnt);
    r_val[REG_W_ADDR_LAG_CNT]     = SW'(w_addr_lag_cnt);
    r_val[REG_W_EARLY_STALL_CNT]  = SW'(w_early_stall_cnt);
    r_val[REG_W_ERR_CNT]          = SW'(w_err_cnt);
    r_val[REG_AR_BURST_CNT]       = SW'(ar_burst_cnt);
    r_val[REG_AR_DEPTH_MAX]       = SW'(rd_outstanding_max);
    r_val[REG_AR_LEN_MIN]         = SW'(arlen_min);
    r_val[REG_AR_LEN_MAX]         = SW'(arlen_max);
    r_val[REG_AR_BYTES_SUM]       = SW'(ar_bytes_sum);
    r_val[REG_AR_BYTES_MIN]       = SW'(ar_bytes_min);
    r_val[REG_AR_BYTES_MAX]       = SW'(ar_bytes_max);
    r_val[REG_R_BURST_CNT]        = SW'(r_burst_cnt);
    r_val[REG_R_DEPTH_MAX]        = SW'(rd_responding_max);
    r_val[REG_R_BEAT_CNT]         = SW'(r_beat_cnt);
    r_val[REG_RD_OUTSTANDING_MAX] = SW'(rd_outstanding_max);
    r_val[REG_RD_MAX_RESP]        = SW'(rd_responding_max);
    r_val[REG_RD_R_STALLS]        = SW'(rd_r_stalls);
    r_val[REG_RD_SLOW_LINK]       = SW'(rd_slow_link);
    r_val[REG_RD_LAG]             = SW'(rd_lag);
    r_val[REG_RD_IDLE_CYCLES]     = SW'(rd_idle_cycles);
    r_val[REG_RD_AR_STALLS]       = SW'(rd_ar_stalls);
    r_val[REG_RD_AR_CYCLES]       = SW'(rd_ar_cycles);
    r_val[REG_R_ERR_CNT]          = SW'(r_err_cnt);
  end

  // TODO: set this and make use of it
  assign stat_err = 1'b0;

  `SVC_UNUSED({m_axi_awaddr, m_axi_awid, m_axi_awburst, m_axi_wdata, m_axi_bid,
               m_axi_araddr, m_axi_arburst, m_axi_rdata});

endmodule
`endif
