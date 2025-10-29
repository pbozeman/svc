`ifndef SVC_ARBITER
`define SVC_ARBITER

`include "svc.sv"
`include "svc_priority_encoder.sv"

//
// Round robin arbiter
//
// The method for this is described in
// https://circuitcove.com/design-examples-rr-arbiter/, but
// this is using LSB priority.
//
module svc_arbiter #(
    parameter NUM_M     = 2,
    parameter IDX_WIDTH = $clog2(NUM_M)
) (
    input logic clk,
    input logic rst_n,

    input  logic [    NUM_M-1:0] request,
    input  logic                 done,
    output logic                 grant_valid,
    output logic [IDX_WIDTH-1:0] grant_idx
);
  logic                 grant_valid_next;
  logic [IDX_WIDTH-1:0] grant_idx_next;

  logic                 pri_valid;
  logic [IDX_WIDTH-1:0] pri_encoded;

  logic                 masked_pri_valid;
  logic [IDX_WIDTH-1:0] masked_pri_encoded;

  logic [    NUM_M-1:0] mask;
  logic [    NUM_M-1:0] mask_next;

  svc_priority_encoder #(
      .WIDTH(NUM_M)
  ) svc_priority_encoder_i (
      .i_unencoded(request),
      .o_valid    (pri_valid),
      .o_encoded  (pri_encoded)
  );

  svc_priority_encoder #(
      .WIDTH(NUM_M)
  ) svc_priority_encoder_masked_i (
      .i_unencoded(request & mask),
      .o_valid    (masked_pri_valid),
      .o_encoded  (masked_pri_encoded)
  );

  always_comb begin
    grant_valid_next = grant_valid;
    grant_idx_next   = grant_idx;
    mask_next        = mask;

    if (!grant_valid || done) begin
      grant_valid_next = 1'b0;

      if (pri_valid) begin
        grant_valid_next = 1'b1;
        if (masked_pri_valid) begin
          grant_idx_next = masked_pri_encoded;
          mask_next      = {NUM_M{1'b1}} << (masked_pri_encoded + 1);
        end else begin
          grant_idx_next = pri_encoded;
          mask_next      = {NUM_M{1'b1}} << (pri_encoded + 1);
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      grant_valid <= 1'b0;
      grant_idx   <= 0;
      mask        <= 0;
    end else begin
      grant_valid <= grant_valid_next;
      grant_idx   <= grant_idx_next;
      mask        <= mask_next;
    end
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_ARBITER
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif
  // Note: the sby file sets NUM_M to a non-power of 2

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  //
  // assumptions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
    end
  end

  //
  // simple assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // grant index is valid when grant_valid is asserted
      if (grant_valid) begin
        `ASSERT(a_grant_ltm, int'(grant_idx) < NUM_M);
      end

      // grants are stable
      if ($past(grant_valid) && !$past(done)) begin
        `ASSERT(a_valid_stable, grant_valid);
        `ASSERT(a_grant_stable, $stable(grant_idx));
      end

      // grant corresponds to an active request
      if (grant_valid) begin
        `ASSERT(a_grant_req, $past(request != 0) || $past(grant_valid && !done
                ));
      end

      // no grants without a request
      if ($past(done && request == 0)) begin
        `ASSERT(a_fantom_grant, !grant_valid);
      end
    end
  end

`ifdef FORMAL_SVC_ARBITER
  // The round robin verification needs at least 3 managers, which may not be
  // the case when used by other modules.

  //
  // round robin
  //
  // verilator lint_off: UNDRIVEN
  logic [IDX_WIDTH-1:0] f_some_m_a;
  logic [IDX_WIDTH-1:0] f_some_m_b;
  logic [IDX_WIDTH-1:0] f_some_m_c;
  // verilator lint_on: UNDRIVEN

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // let the solver pick some managers, but enforce an ordering: A < B < C
      assume ($stable(f_some_m_a));
      assume ($stable(f_some_m_b));
      assume ($stable(f_some_m_c));
      assume (f_some_m_a < f_some_m_b && f_some_m_b < f_some_m_c);

      // if a grant was just released...
      if (grant_valid && $past(grant_valid && done)) begin
        // when releasing a grant from A, we can only grant to C if B didn't
        // request a grant.
        if ($past(grant_idx == f_some_m_a)) begin
          if (grant_idx == f_some_m_c) begin
            `ASSERT(a_rr, $past((request & 1 << f_some_m_b) == 0));
          end
        end

        // Can only grant to same index if no other requests existed
        if (grant_idx == $past(grant_idx)) begin
          `ASSERT(a_pri_no_other_reqs, $past(request & ~(1 << grant_idx)) == 0);
        end
      end
    end
  end
`endif

  //
  // covers
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `COVER(c_grant_cycle, $past(grant_valid) && $past(done) && grant_valid);
      `COVER(c_all_requests, &request);
    end
  end

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule

`endif
