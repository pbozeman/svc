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
//
// Implementation note: one would think it should be possible to do
// .WIDTH($bits(signal)) directly when instantiating the module, but
// iverilog reduced the example above to 1 bit. Making a signal first
// and then doing a $bits on that intermediate symbol works, whereas
// doing $bits(signal) directly during module instantiation, did not.

`define SVC_UNUSED(signal)                            \
  logic [$bits(signal)-1:0] svc_unused_sig_`__LINE__; \
  svc_unused #(                                       \
    .WIDTH($bits(svc_unused_sig_`__LINE__))           \
  ) svc_unused_`__LINE__ (                            \
    .bits(signal)                                     \
  );

module svc_unused #(
    parameter WIDTH
) (
    // verilator lint_off: UNUSEDSIGNAL
    input logic [WIDTH-1:0] bits
    // verilator lint_on: UNUSEDSIGNAL
);
endmodule

`endif
