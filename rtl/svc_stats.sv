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

`endif
