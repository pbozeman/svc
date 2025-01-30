`ifndef SVC_AXI_STRIPE_ADDR_SV
`define SVC_AXI_STRIPE_ADDR_SV

`include "svc.sv"

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

module svc_axi_stripe_addr #(
    parameter NUM_S            = 2,
    parameter AXI_ADDR_WIDTH   = 16,
    parameter AXI_DATA_WIDTH   = 8,
    parameter S_AXI_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(NUM_S),
    parameter S_WIDTH          = $clog2(NUM_S)
) (
    input  logic [  AXI_ADDR_WIDTH-1:0] s_axi_axaddr,
    output logic [         S_WIDTH-1:0] sub_idx,
    output logic                        word_aligned,
    output logic [S_AXI_ADDR_WIDTH-1:0] m_axi_axaddr
);
  localparam O_WIDTH = $clog2(AXI_DATA_WIDTH / 8);

  assign sub_idx = s_axi_axaddr[S_WIDTH+O_WIDTH-1:O_WIDTH];

  // we can only select the byte offset if the bus size more than a byte wide,
  // otherwise we'll try to select -1:0 from the addr.
  if (O_WIDTH > 0) begin : gen_multi_byte_word
    assign m_axi_axaddr = {
      s_axi_axaddr[AXI_ADDR_WIDTH-1 : S_WIDTH+O_WIDTH],
      s_axi_axaddr[O_WIDTH-1 : 0]
    };
    assign word_aligned = !(&s_axi_axaddr[O_WIDTH-1:0]);
  end else begin : gen_single_byte_word
    assign m_axi_axaddr = s_axi_axaddr[AXI_ADDR_WIDTH-1 : S_WIDTH];
    assign word_aligned = 1'b1;
  end

endmodule

`endif
