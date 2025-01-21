`ifndef SVC_SV
`define SVC_SV

// verilog_format: off
`timescale 1ns / 1ps
`default_nettype none
// verilog_format: on

`define SVC_MAX_AXSIZE(dw) 3'($clog2(dw) - 3)

`endif
