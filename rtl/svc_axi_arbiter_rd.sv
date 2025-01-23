`ifndef SVC_AXI_ARBITER_RD_SV
`define SVC_AXI_ARBITER_RD_SV

`include "svc.sv"
`include "svc_arbiter.sv"
`include "svc_skidbuf.sv"

//
// AXI read arbiter from N managers to 1 subordinate.
//
module svc_axi_arbiter_rd #(
    parameter NUM_M          = 2,
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter M_AXI_ID_WIDTH = AXI_ID_WIDTH + $clog2(NUM_M)
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface for N managers
    //
    input  logic [NUM_M-1:0]                     s_axi_arvalid,
    input  logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [NUM_M-1:0][AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [NUM_M-1:0][               7:0] s_axi_arlen,
    input  logic [NUM_M-1:0][               2:0] s_axi_arsize,
    input  logic [NUM_M-1:0][               1:0] s_axi_arburst,
    output logic [NUM_M-1:0]                     s_axi_arready,
    output logic [NUM_M-1:0]                     s_axi_rvalid,
    output logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [NUM_M-1:0][AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [NUM_M-1:0][               1:0] s_axi_rresp,
    output logic [NUM_M-1:0]                     s_axi_rlast,
    input  logic [NUM_M-1:0]                     s_axi_rready,

    //
    // Manager interface to our subordinate
    //
    output logic                      m_axi_arvalid,
    output logic [M_AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [M_AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready
);
  // id + addr + len + size + burst
  localparam SKIDBUF_AR_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2;

  // id + data + resp + last
  localparam SKIDBUF_R_WIDTH = AXI_ID_WIDTH + AXI_DATA_WIDTH + 2 + 1;

  localparam GRANT_IDX_WIDTH = $clog2(NUM_M);

  // TODO: maybe put this into the arbiter, since it seems that this will be
  // a common need. Wait to see if that unfolds, and do it if so, otherwise,
  // remove this comment.
  logic [          NUM_M-1:0]                     request_mask;

  logic                                           grant_valid;
  logic [GRANT_IDX_WIDTH-1:0]                     grant_idx;

  logic [          NUM_M-1:0]                     sb_arvalid;
  logic [          NUM_M-1:0][  AXI_ID_WIDTH-1:0] sb_arid;
  logic [          NUM_M-1:0][AXI_ADDR_WIDTH-1:0] sb_araddr;
  logic [          NUM_M-1:0][               7:0] sb_arlen;
  logic [          NUM_M-1:0][               2:0] sb_arsize;
  logic [          NUM_M-1:0][               1:0] sb_arburst;

  logic [          NUM_M-1:0]                     sb_rready;

  logic [   AXI_ID_WIDTH-1:0]                     r_rid;
  logic [GRANT_IDX_WIDTH-1:0]                     r_grant_idx;

  //-------------------------------------------------------------------------
  //
  // Read request/address processing
  //
  //-------------------------------------------------------------------------

  // ar channel skid buffers
  for (genvar i = 0; i < NUM_M; i++) begin : gen_ar_sb
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_AR_WIDTH)
    ) svc_skidbuf_ar_i (
        .clk(clk),
        .rst_n(rst_n),
        .i_valid(s_axi_arvalid[i] && s_axi_arready[i]),
        .i_data({
          s_axi_arid[i],
          s_axi_araddr[i],
          s_axi_arlen[i],
          s_axi_arsize[i],
          s_axi_arburst[i]
        }),
        .o_ready(s_axi_arready[i]),
        .i_ready(grant_valid && grant_idx == i && m_axi_arready),
        .o_data({
          sb_arid[i], sb_araddr[i], sb_arlen[i], sb_arsize[i], sb_arburst[i]
        }),
        .o_valid(sb_arvalid[i])
    );
  end

  // arbiter
  //
  // If we have the grant, we don't want to request it again because the sb
  // will still be valid until ready raises.
  assign request_mask = grant_valid ? ~(1 << grant_idx) : '1;

  svc_arbiter #(
      .NUM_M(NUM_M)
  ) svc_arbiter_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .request    (sb_arvalid & request_mask),
      .done       (m_axi_arvalid && m_axi_arready),
      .grant_valid(grant_valid),
      .grant_idx  (grant_idx)
  );

  // mux our signal stream
  assign m_axi_arvalid = grant_valid;
  assign m_axi_arid = grant_valid ? {grant_idx, sb_arid[grant_idx]} : 0;
  assign m_axi_araddr = grant_valid ? sb_araddr[grant_idx] : 0;
  assign m_axi_arlen = grant_valid ? sb_arlen[grant_idx] : 0;
  assign m_axi_arsize = grant_valid ? sb_arsize[grant_idx] : 0;
  assign m_axi_arburst = grant_valid ? sb_arburst[grant_idx] : 0;

  //-------------------------------------------------------------------------
  //
  // Read response processing
  //
  //-------------------------------------------------------------------------

  assign {r_grant_idx, r_rid} = m_axi_rid;
  assign m_axi_rready = m_axi_rvalid ? sb_rready[r_grant_idx] : 1'b0;

  //
  // r channel skid buffers
  //
  // Note: these also are doing the muxed responses
  //
  for (genvar i = 0; i < NUM_M; i++) begin : gen_r_sb
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_R_WIDTH),
        .OPT_OUTREG(1)
    ) svc_skidbuf_r_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(r_grant_idx == i && m_axi_rvalid),
        .i_data ({r_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast}),
        .o_ready(sb_rready[i]),

        .i_ready(s_axi_rvalid[i] && s_axi_rready[i]),
        .o_data({s_axi_rid[i], s_axi_rdata[i], s_axi_rresp[i], s_axi_rlast[i]}),
        .o_valid(s_axi_rvalid[i])
    );
  end

endmodule
`endif
