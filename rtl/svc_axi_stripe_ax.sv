`ifndef SVC_AXI_STRIPE_AX_SV
`define SVC_AXI_STRIPE_AX_SV

`include "svc.sv"

// Take an incoming subordinate burstable addr and len and split them
// into subordinate addr and len signals.
//
// Note: this is purely combinatorial at the moment. The callers are supposed
// to register the outputs before sending them to the subordinates, although,
// this might need to get clocked in the future if timing becomes an issue.
//
// It's quite a bit of combinatorial logic as we have to do the addr
// and starting stripe calculation before we can determine the valid bits and
// axlen signals for the subordinates. This wouldn't be the case if stripe
// IO was aligned, with no partial stripe io.
//
// If timing becomes an issue, it might be worthwhile to make a stripe module
// that expects fully aligned, full width, io to avoid calculation latency for
// well behaving modules, and then take this module and use it to wrap the
// higher perf module for poorly behaving callers.
//
// Note: if this gets clocked, it might be nice to just take over the whole ax
// stream, and do the hand shaking on behalf of the caller.
module svc_axi_stripe_ax #(
    parameter NUM_S            = 2,
    parameter AXI_ADDR_WIDTH   = 16,
    parameter AXI_DATA_WIDTH   = 8,
    parameter S_AXI_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(NUM_S),
    parameter S_WIDTH          = $clog2(NUM_S)
) (
    input logic [AXI_ADDR_WIDTH-1:0] s_addr,
    input logic [               7:0] s_len,

    output logic [S_WIDTH-1:0] start_idx,
    output logic               alignment_error,

    output logic [NUM_S-1:0]                       m_valid,
    output logic [NUM_S-1:0][S_AXI_ADDR_WIDTH-1:0] m_addr,
    output logic [NUM_S-1:0][                 7:0] m_len
);
  localparam O_WIDTH = $clog2(AXI_DATA_WIDTH / 8);

  logic [S_AXI_ADDR_WIDTH-1:0] axaddr;

  //-------------------------------------------------------------------------
  //
  // start_idx
  //
  //-------------------------------------------------------------------------
  assign start_idx = s_addr[S_WIDTH+O_WIDTH-1:O_WIDTH];

  //-------------------------------------------------------------------------
  //
  // axaddr
  //
  // We are striping based on words, but since AXI addrs are byte based we can't
  // just bit shift off the lower bits. We have to cut out the part of the
  // address used to select subordinate, keeping the upper addr and lower
  // byte bits. See the following diagram:
  //
  // +-----------------------+-------------------+-----------------+
  // |    High bits          | Subordinate Index |  Byte Offset    |
  // +-----------------------+-------------------+-----------------+
  //  ^                     ^                   ^                 ^
  //  [AXI_ADDR_WIDTH-1 :   (S_WIDTH+O_WIDTH) : O_WIDTH         : 0]
  //
  //  Note: when going to real hw like an SRAM chip that uses word based
  //  addresses, the byte offset will get shifted off too, but we can't
  //  do that here for the reasons described above.
  //
  //-------------------------------------------------------------------------

  // we can only select the byte offset if the bus size more than a byte wide,
  // otherwise we'll try to select -1:0 from the addr.
  if (O_WIDTH > 0) begin : gen_multi_byte_word
    assign axaddr = {
      s_addr[AXI_ADDR_WIDTH-1 : S_WIDTH+O_WIDTH], s_addr[O_WIDTH-1 : 0]
    };
    assign alignment_error = |s_addr[O_WIDTH-1:0];
  end else begin : gen_single_byte_word
    assign axaddr          = {s_addr[AXI_ADDR_WIDTH-1 : S_WIDTH]};
    assign alignment_error = 1'b0;
  end

  assign m_addr = {NUM_S{axaddr}};

  //-------------------------------------------------------------------------
  //
  // axlen
  //
  //-------------------------------------------------------------------------

  // total_beats is the actual beats count not len in axi terms (i.e. it's +1,
  // which makes the remainder math easier.)
  logic [8:0] total_beats;
  assign total_beats = s_len + 1;

  // the number of full stripes we are writing, if there are no partial
  // stripes, this is also the number of beats per subordinate
  logic [7:0] full_stripes;
  assign full_stripes = 8'(total_beats >> S_WIDTH);

  // the remaining beats due to a partial stripe io, i.e. axlen wasn't
  // a multiple of NUM_S. We distribute this many +1 beats to the subordinates
  // at the end of the io.
  logic [S_WIDTH-1:0] partial_beats;
  assign partial_beats = S_WIDTH'(total_beats & 9'(((1 << S_WIDTH) - 1)));

  // I tried a version that had less going on in the loops in the always_comb,
  // and did more with masking, etc. Yosys reported the exact same cell count
  // for both, so I kept this version as it's conceptually simpler to
  // understand.
  always_comb begin
    m_valid = '0;
    m_len   = '0;

    // if we have more than a stripe worth of io, then all subordinates will
    // be participating. Set them all.
    if (full_stripes > 0) begin
      for (int i = 0; i < NUM_S; i++) begin
        m_valid[i] = 1'b1;
        m_len[i]   = full_stripes - 1;
      end
    end

    // If we have a partial stripe io, either as the first stripe or after
    // doing some full stripe io, bump the len for the subordinates
    // participating in the partial stripe io. If our only io is a partial
    // stripe, we won't have set valid above, so do it here.
    for (int i = 0; i < NUM_S; i++) begin
      logic [S_WIDTH-1:0] idx;
      idx = (start_idx + S_WIDTH'(i)) & S_WIDTH'(NUM_S - 1);
      if (i < partial_beats) begin
        m_valid[idx] = 1'b1;
        m_len[idx]   = full_stripes;
      end
    end
  end

endmodule

`endif
