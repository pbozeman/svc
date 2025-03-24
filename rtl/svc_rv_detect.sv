`ifndef SVC_RV_DETECT_SV
`define SVC_RV_DETECT_SV

// ready/valid handshake detector
//
// This is designed for use by modules that are passively watching a
// bus with ready/valid handshaking, e.g. the plan is to use it on
// all the ready/valid handshakes in an axi stats module.

module svc_rv_detect (
    input logic clk,
    input logic rst_n,

    input logic valid,
    input logic ready,

    output logic txn_started,
    output logic txn_stalled,
    output logic txn_accepted
);
  logic txn_active;

  always @(posedge clk) begin
    if (!rst_n) begin
      txn_active   <= 1'b0;
      txn_started  <= 1'b0;
      txn_accepted <= 1'b0;
      txn_stalled  <= 1'b0;
    end else begin
      txn_started <= valid && !txn_active;
      txn_stalled <= txn_active && !ready;

      if (valid && !ready) begin
        txn_active   <= 1'b1;
        txn_accepted <= 1'b0;
      end else if (valid && ready) begin
        txn_accepted <= 1'b1;
        txn_active   <= 1'b0;
      end else if (!valid) begin
        txn_active   <= 1'b0;
        txn_accepted <= 1'b0;
      end
    end
  end

endmodule
`endif
