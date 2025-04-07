`ifndef SVC_STATS_SV
`define SVC_STATS_SV

// TODO: these need tuning. They also should use some form of fpga
// architecture, rather than the tool being used to synthesize.
// For now, this is the way the default for an ice40 vs. a
// xilinx chip is getting set (albeit crudely)
`ifdef SYNTH_YOSYS
`define SVC_PIPE_BPS 4
`else
`define SVC_PIPE_BPS 16
`endif

`define SVC_STAT_CNT(stat_width, name, inc_expr, dec_expr = 1'b0)          \
  logic [stat_width-1:0] name;                                             \
  svc_stats_cnt #(                                                         \
      .STAT_WIDTH(stat_width)                                              \
  ) svc_stats_cnt_``name`` (                                               \
      .clk(clk),                                                           \
      .rst_n(rst_n),                                                       \
      .clr(stat_clear),                                                    \
      .inc(inc_expr),                                                      \
      .dec(dec_expr),                                                      \
      .cnt(name)                                                           \
  )

`define SVC_STAT_CNT_EN(stat_width, name)                                  \
  logic [stat_width-1:0] name;                                             \
  logic name``_en;                                                         \
  svc_stats_cnt #(                                                         \
      .STAT_WIDTH(stat_width)                                              \
  ) svc_stats_cnt_``name`` (                                               \
      .clk(clk),                                                           \
      .rst_n(rst_n),                                                       \
      .clr(stat_clear),                                                    \
      .inc(name``_en),                                                     \
      .dec(1'b0),                                                          \
      .cnt(name)                                                           \
  )

`define SVC_STAT_MIN(val_width, name, val_expr, en_expr = 1'b1)            \
  logic [val_width-1:0] name``_min;                                        \
  svc_stats_min #(                                                         \
      .WIDTH(val_width)                                                    \
  ) svc_stats_min_``name`` (                                               \
      .clk(clk),                                                           \
      .rst_n(rst_n),                                                       \
      .clr(stat_clear),                                                    \
      .en(en_expr),                                                        \
      .val(val_expr),                                                      \
      .min(name``_min)                                                     \
  )

`define SVC_STAT_MAX(val_width, name, val_expr, en_expr = 1'b1)            \
  logic [val_width-1:0] name``_max;                                        \
  svc_stats_max #(                                                         \
      .WIDTH(val_width)                                                    \
  ) svc_stats_max_``name`` (                                               \
      .clk(clk),                                                           \
      .rst_n(rst_n),                                                       \
      .clr(stat_clear),                                                    \
      .en(en_expr),                                                        \
      .val(val_expr),                                                      \
      .max(name``_max)                                                     \
  )

`define SVC_STAT_MIN_MAX(val_width, name, val_expr, en_expr = 1'b1)        \
  `SVC_STAT_MIN(val_width, name, val_expr, en_expr);                       \
  `SVC_STAT_MAX(val_width, name, val_expr, en_expr)

`define SVC_STAT_VAL(stat_width, val_width, name, val_expr, en_expr)       \
  logic [val_width-1:0] name``_min;                                        \
  logic [val_width-1:0] name``_max;                                        \
  logic [STAT_WIDTH-1:0] name``_sum;                                       \
  svc_stats_val #(                                                         \
      .WIDTH(val_width),                                                   \
      .STAT_WIDTH(stat_width)                                              \
  ) svc_stats_val_``name`` (                                               \
      .clk(clk),                                                           \
      .rst_n(rst_n),                                                       \
      .clr(stat_clear),                                                    \
      .en(en_expr),                                                        \
      .val(val_expr),                                                      \
      .min(name``_min),                                                    \
      .max(name``_max),                                                    \
      .sum(name``_sum)                                                     \
  )

`endif
