`ifndef SVC_SKIDBUF_SV
`define SVC_SKIDBUF_SV

`include "svc.sv"

// Port of https://zipcpu.com/blog/2019/05/22/skidbuffer.html.
//
// Moved to the svc coding style and stripping out some of the extra
// complexity (e.g. options other than output registration).

module svc_skidbuf #(
    parameter DATA_WIDTH = 8,
    parameter OPT_OUTREG = 0
) (
    input logic clk,
    input logic rst_n,

    input  logic                  i_valid,
    input  logic [DATA_WIDTH-1:0] i_data,
    output logic                  o_ready,

    output logic                  o_valid,
    input  logic                  i_ready,
    output logic [DATA_WIDTH-1:0] o_data
);
  logic                  skid_i_valid;
  logic [DATA_WIDTH-1:0] skid_i_data;

  //
  // s side
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      skid_i_valid <= 0;
    end else begin
      if ((i_valid && o_ready) && (o_valid && !i_ready))
        // We have incoming data, but the output is stalled
        skid_i_valid <= 1;
      else if (i_ready) skid_i_valid <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if ((!OPT_OUTREG || i_valid) && o_ready) begin
      skid_i_data <= i_data;
    end
  end

  assign o_ready = !skid_i_valid;

  //
  // m side
  //
  if (!OPT_OUTREG) begin : gen_net_output
    assign o_valid = rst_n && (i_valid || skid_i_valid);

    always_comb begin
      if (skid_i_valid) begin
        o_data = skid_i_data;
      end else if (i_valid) begin
        o_data = i_data;
      end else begin
        o_data = 0;
      end
    end

  end else begin : gen_reg_output
    logic o_valid_reg;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        o_valid_reg <= 0;
      end else if (!o_valid || i_ready) begin
        o_valid_reg <= (i_valid || skid_i_valid);
      end
    end

    assign o_valid = o_valid_reg;

    always_ff @(posedge clk) begin
      if (!o_valid || i_ready) begin
        if (skid_i_valid) begin
          o_data <= skid_i_data;
        end else if (i_valid) begin
          o_data <= i_data;
        end
      end
    end
  end
endmodule
`endif
