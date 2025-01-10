`ifndef SVC_UNUSED
`define SVC_UNSUED

// Helper macro to mark bits unused without having to clutter up files with
// verilat0r comments. This is particularly helpful when dropping bits from
// something like a byte addr to word addr translation, e.g:
//
//   `SVC_UNUSED(s_axil_araddr[LSB-1:0]);
//
// Note, multiple signals can be passed with concatenation, e.g. in a module
// that is largely doing pass through to an aysnc device and doesn't use it's
// clock:
//
//   `SVC_UNUSED({clk, rst_n, s_axil_araddr[LSB-1:0]});

`ifndef FORMAL
`define SVC_UNUSED(signal)                            \
  svc_unused svc_unused_i (                           \
    .unused(& signal)                                 \
  );

module svc_unused (
    // verilator lint_off: UNUSEDSIGNAL
    input logic unused
    // verilator lint_on: UNUSEDSIGNAL
);
endmodule
`else
`define SVC_UNUSED(signal)
`endif

`endif
