`ifndef SVC_RGB_SV
`define SVC_RGB_SV

// verilog_format: off
// The adding and dividing of the numerator gets closer to real values with
// integer truncation, i.e. final value of 0.94 becomes 1 instead of 0 with
// this approach.
`define SVC_RGB_M_TO_N(c, m, n) \
  n'(((c) * ((1 << n) - 1) + ((1 << m) - 1) / 2) / ((1 << m) - 1))
// verilog_format: on

`endif
