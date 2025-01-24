`ifndef SVC_AXI_STRIPE_RD_SV
`define SVC_AXI_STRIPE_RD_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Stripe read requests from 1 manager to N subordinates based on the low
// order bits in the address. There are some requirements for usage:
//
//  * NUM_S must be a power of 2.
//  * s_axi_araddr must be stripe aligned.
//  * s_axi_arsize must be for the full data width.
//  * s_axi_arlen must end on a stripe boundary
//
// These requirements could be lifted, but would introduce more complexity
// into this module, and would likely come with a performance cost on the
// boundaries. It's better if the caller just does the right thing.
//
// TODO: check assumptions and return a rresp error if they don't hold, for
// now, rely on the asserts during formal verification to catch misuse.
//
module svc_axi_stripe_rd #(
    parameter NUM_S            = 2,
    parameter AXI_ADDR_WIDTH   = 8,
    parameter AXI_DATA_WIDTH   = 16,
    parameter AXI_ID_WIDTH     = 4,
    parameter S_AXI_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(NUM_S)
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_arready,
    output logic                      s_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,
    input  logic                      s_axi_rready,

    //
    // Manager interface to our subordinates
    //
    output logic [NUM_S-1:0]                       m_axi_arvalid,
    output logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [NUM_S-1:0][S_AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [NUM_S-1:0][                 7:0] m_axi_arlen,
    output logic [NUM_S-1:0][                 2:0] m_axi_arsize,
    output logic [NUM_S-1:0][                 1:0] m_axi_arburst,
    input  logic [NUM_S-1:0]                       m_axi_arready,
    input  logic [NUM_S-1:0]                       m_axi_rvalid,
    input  logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [NUM_S-1:0][  AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [NUM_S-1:0][                 1:0] m_axi_rresp,
    input  logic [NUM_S-1:0]                       m_axi_rlast,
    output logic [NUM_S-1:0]                       m_axi_rready
);
  localparam S_WIDTH = $clog2(NUM_S);

  logic                                     s_axi_arready_next;

  logic [  NUM_S-1:0]                       addr_ready;
  logic [  NUM_S-1:0]                       addr_ready_next;

  logic                                     reads_ready;
  logic                                     reads_ready_next;

  logic [  NUM_S-1:0]                       m_axi_arvalid_next;
  logic [  NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_arid_next;
  logic [  NUM_S-1:0][S_AXI_ADDR_WIDTH-1:0] m_axi_araddr_next;
  logic [  NUM_S-1:0][                 7:0] m_axi_arlen_next;
  logic [  NUM_S-1:0][                 2:0] m_axi_arsize_next;
  logic [  NUM_S-1:0][                 1:0] m_axi_arburst_next;

  logic [S_WIDTH-1:0]                       idx;
  logic [S_WIDTH-1:0]                       idx_next;

  //-------------------------------------------------------------------------
  //
  // AR channel
  //
  //-------------------------------------------------------------------------

  for (genvar i = 0; i < NUM_S; i++) begin : gen_init
    always @(*) begin
      addr_ready_next[i]    = addr_ready[i];

      m_axi_arvalid_next[i] = m_axi_arvalid[i] && !m_axi_arready[i];
      m_axi_arid_next[i]    = m_axi_arid[i];
      m_axi_araddr_next[i]  = m_axi_araddr[i];
      m_axi_arlen_next[i]   = m_axi_arlen[i];
      m_axi_arsize_next[i]  = m_axi_arsize[i];
      m_axi_arburst_next[i] = m_axi_arburst[i];

      if (s_axi_arready && s_axi_arvalid) begin
        addr_ready_next[i]    = 1'b0;

        m_axi_arvalid_next[i] = 1'b1;
        m_axi_arid_next[i]    = s_axi_arid;
        m_axi_araddr_next[i]  = s_axi_araddr[AXI_ADDR_WIDTH-1:S_WIDTH];
        m_axi_arsize_next[i]  = s_axi_arsize;
        m_axi_arburst_next[i] = s_axi_arburst;
        m_axi_arlen_next[i]   = s_axi_arlen >> S_WIDTH;
      end else begin
        if (m_axi_arvalid[i] && m_axi_arready[i]) begin
          addr_ready_next[i] = 1'b1;
        end
      end
    end
  end

  always_comb begin
    s_axi_arready_next = &addr_ready && reads_ready;

    if (s_axi_arready && s_axi_arvalid) begin
      s_axi_arready_next = 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      addr_ready    <= '1;
      s_axi_arready <= 1'b1;

      m_axi_arvalid <= '0;
    end else begin
      addr_ready    <= addr_ready_next;
      s_axi_arready <= s_axi_arready_next;

      m_axi_arvalid <= m_axi_arvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axi_arid    <= m_axi_arid_next;
    m_axi_araddr  <= m_axi_araddr_next;
    m_axi_arlen   <= m_axi_arlen_next;
    m_axi_arsize  <= m_axi_arsize_next;
    m_axi_arburst <= m_axi_arburst_next;
  end

  //-------------------------------------------------------------------------
  //
  // index iteration
  //
  // (since NUM_S is a power of 2, we don't have to check against a max value,
  // we can just wrap)
  //
  //-------------------------------------------------------------------------
  always_comb begin
    idx_next = idx;

    if (s_axi_rvalid && s_axi_rready) begin
      idx_next = idx + 1;
    end

    if (s_axi_arready && s_axi_arvalid) begin
      idx_next = 0;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      idx <= 0;
    end else begin
      idx <= idx_next;
    end
  end

  //-------------------------------------------------------------------------
  //
  // r channel
  //
  //-------------------------------------------------------------------------

  // r channel signals from caller to active subordinate
  always_comb begin
    m_axi_rready      = '0;
    m_axi_rready[idx] = s_axi_rready;
  end

  // r channel from subordinate back to caller
  always_comb begin
    s_axi_rvalid = m_axi_rvalid[idx];
    s_axi_rid    = m_axi_rid[idx];
    s_axi_rdata  = m_axi_rdata[idx];
    s_axi_rresp  = m_axi_rresp[idx];

    // only propagate the rlast bit from the last subordinate
    s_axi_rlast  = m_axi_rlast[idx] && idx == '1;
  end

  always_comb begin
    reads_ready_next = reads_ready;

    if (s_axi_arready && s_axi_arvalid) begin
      reads_ready_next = 1'b0;
    end

    if (s_axi_rvalid && s_axi_rready && s_axi_rlast) begin
      reads_ready_next = 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      reads_ready <= 1'b1;
    end else begin
      reads_ready <= reads_ready_next;
    end
  end

  `SVC_UNUSED({s_axi_araddr[S_WIDTH-1:0]});

`ifdef FORMAL
  // Formal testing happens in the combined module, but we do have asserts
  // regarding bad behavior of the callers.
  //
  // Note: if formal verification is added to this module in the future, these
  // should use the ASSUME/ASSERT macros to be assumes for this module, but
  // asserts when used as a submodule.
  always @(posedge clk) begin
    if (rst_n) begin
      assert (NUM_S % 2 == 0);

      // the following are assertions about the requirements for usage
      // documented at the top of the module
      if (s_axi_arvalid) begin
        // Address must be stripe aligned - lower bits should be zero
        assert (s_axi_araddr[S_WIDTH-1:0] == '0);

        // Size must match full data width
        assert (int'(s_axi_arsize) == $clog2(AXI_DATA_WIDTH / 8));

        // Length must end on stripe boundary
        assert (((s_axi_arlen + 1) % NUM_S) == 0);
      end
    end
  end
`endif

endmodule
`endif
