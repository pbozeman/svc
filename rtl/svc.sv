`ifndef SVC_SV
`define SVC_SV

`timescale 1ns / 1ps

// Vivado doesn't seem to be following the sv standard and forces one
// to use 'input wire logic <signal>' rather than 'input logic <signal>' when
// the default net type is none.
//
// See:
//   https://adaptivesupport.amd.com/s/question/0D52E00006iHwnKSAS/vivado-synthesis-error-synth-86735-cause-by-using-defaultnettype-none
// and
//   https://stackoverflow.com/questions/52173730/systemverilog-changing-port-type-from-wire-to-logic-gives-error-when-usingn-defa
`ifdef SVC_DEF_NET_NONE
`default_nettype none
`endif

`define SVC_MAX_AXSIZE(dw) 3'($clog2(dw) - 3)

`endif
