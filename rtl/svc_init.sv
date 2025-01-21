`ifndef SVC_INIT_SV
`define SVC_INIT_SV

`include "svc.sv"

module svc_init #(
    parameter RST_CYCLES = 15
) (
    input  logic clk,
    output logic rst_n = 1'b0
);
  logic [$clog2(RST_CYCLES)-1:0] cnt = 0;

  always_ff @(posedge clk) begin
    if (cnt < RST_CYCLES) begin
      cnt   <= cnt + 1;
      rst_n <= 1'b0;
    end else begin
      rst_n <= 1'b1;
    end
  end
endmodule

`endif
