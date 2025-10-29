`ifndef SVC_AXIL_ROUTER_SV
`define SVC_AXIL_ROUTER_SV

`include "svc.sv"
`include "svc_unused.sv"
`include "svc_axil_router_rd.sv"
`include "svc_axil_router_wr.sv"

//
// Route AXIL manager to 1 of N subordinates
//
module svc_axil_router #(
    parameter S_AXIL_ADDR_WIDTH = 32,
    parameter S_AXIL_DATA_WIDTH = 16,
    parameter M_AXIL_ADDR_WIDTH = 32,
    parameter M_AXIL_DATA_WIDTH = 16,
    parameter NUM_S             = 2
) (
    input logic clk,
    input logic rst_n,

    // subordinate interface for our manager
    input  logic                         s_axil_awvalid,
    input  logic [S_AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    output logic                         s_axil_awready,

    input  logic                           s_axil_wvalid,
    input  logic [  S_AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [S_AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    output logic                           s_axil_wready,

    output logic       s_axil_bvalid,
    output logic [1:0] s_axil_bresp,
    input  logic       s_axil_bready,

    input  logic                         s_axil_arvalid,
    input  logic [S_AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                         s_axil_arready,

    output logic                         s_axil_rvalid,
    output logic [S_AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                  1:0] s_axil_rresp,
    input  logic                         s_axil_rready,

    // manager interfaces to our subordinates
    output logic [NUM_S-1:0]                        m_axil_awvalid,
    output logic [NUM_S-1:0][M_AXIL_ADDR_WIDTH-1:0] m_axil_awaddr,
    input  logic [NUM_S-1:0]                        m_axil_awready,

    output logic [NUM_S-1:0]                          m_axil_wvalid,
    output logic [NUM_S-1:0][  M_AXIL_DATA_WIDTH-1:0] m_axil_wdata,
    output logic [NUM_S-1:0][M_AXIL_DATA_WIDTH/8-1:0] m_axil_wstrb,
    input  logic [NUM_S-1:0]                          m_axil_wready,

    input  logic [NUM_S-1:0]      m_axil_bvalid,
    input  logic [NUM_S-1:0][1:0] m_axil_bresp,
    output logic [NUM_S-1:0]      m_axil_bready,

    output logic [NUM_S-1:0]                        m_axil_arvalid,
    output logic [NUM_S-1:0][M_AXIL_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic [NUM_S-1:0]                        m_axil_arready,

    input  logic [NUM_S-1:0]                        m_axil_rvalid,
    input  logic [NUM_S-1:0][M_AXIL_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [NUM_S-1:0][                  1:0] m_axil_rresp,
    output logic [NUM_S-1:0]                        m_axil_rready
);
  svc_axil_router_wr #(
      .S_AXIL_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .S_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .M_AXIL_ADDR_WIDTH(M_AXIL_ADDR_WIDTH),
      .M_AXIL_DATA_WIDTH(M_AXIL_DATA_WIDTH),
      .NUM_S            (NUM_S)
  ) svc_axil_router_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awvalid(s_axil_awvalid),
      .s_axil_awaddr (s_axil_awaddr),
      .s_axil_awready(s_axil_awready),
      .s_axil_wvalid (s_axil_wvalid),
      .s_axil_wdata  (s_axil_wdata),
      .s_axil_wstrb  (s_axil_wstrb),
      .s_axil_wready (s_axil_wready),
      .s_axil_bvalid (s_axil_bvalid),
      .s_axil_bresp  (s_axil_bresp),
      .s_axil_bready (s_axil_bready),

      .m_axil_awvalid(m_axil_awvalid),
      .m_axil_awaddr (m_axil_awaddr),
      .m_axil_awready(m_axil_awready),
      .m_axil_wvalid (m_axil_wvalid),
      .m_axil_wdata  (m_axil_wdata),
      .m_axil_wstrb  (m_axil_wstrb),
      .m_axil_wready (m_axil_wready),
      .m_axil_bvalid (m_axil_bvalid),
      .m_axil_bresp  (m_axil_bresp),
      .m_axil_bready (m_axil_bready)
  );

  svc_axil_router_rd #(
      .S_AXIL_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .S_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .M_AXIL_ADDR_WIDTH(M_AXIL_ADDR_WIDTH),
      .M_AXIL_DATA_WIDTH(M_AXIL_DATA_WIDTH),
      .NUM_S            (NUM_S)
  ) svc_axil_router_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arready(s_axil_arready),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rready (s_axil_rready),

      .m_axil_arvalid(m_axil_arvalid),
      .m_axil_araddr (m_axil_araddr),
      .m_axil_arready(m_axil_arready),
      .m_axil_rvalid (m_axil_rvalid),
      .m_axil_rdata  (m_axil_rdata),
      .m_axil_rresp  (m_axil_rresp),
      .m_axil_rready (m_axil_rready)
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_AXIL_ROUTER
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  always @(posedge clk) begin
    if (rst_n) begin
      // Check that we don't activate multiple subordinates simultaneously
      // on AW channel
      `ASSERT(a_aw_onehot, $onehot0(m_axil_awvalid));

      // Check that we don't activate multiple subordinates simultaneously
      // on W channel
      `ASSERT(a_w_onehot, $onehot0(m_axil_wvalid));

      // Check that we don't activate multiple subordinates simultaneously
      // on AR channel
      `ASSERT(a_ar_onehot, $onehot0(m_axil_arvalid));
    end
  end

`ifdef FORMAL_SVC_AXIL_ROUTER
  // the number of bits necessary to count the maximum number
  // of items in flight.
  localparam F_LGDEPTH = 4;

  logic f_past_valid;
  initial f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  faxil_slave #(
      .C_AXI_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .F_LGDEPTH       (F_LGDEPTH),
      .F_OPT_INITIAL   (0),
      .F_AXI_MAXWAIT   (2),
      .F_AXI_MAXDELAY  (4),
      .F_AXI_MAXRSTALL (4)
  ) faxil_sub_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      .i_axi_awready(s_axil_awready),
      .i_axi_awaddr (s_axil_awaddr),
      .i_axi_awvalid(s_axil_awvalid),
      .i_axi_awprot ('0),

      .i_axi_wready(s_axil_wready),
      .i_axi_wdata (s_axil_wdata),
      .i_axi_wstrb (s_axil_wstrb),
      .i_axi_wvalid(s_axil_wvalid),

      .i_axi_bready(s_axil_bready),
      .i_axi_bvalid(s_axil_bvalid),
      .i_axi_bresp (s_axil_bresp),

      .i_axi_araddr (s_axil_araddr),
      .i_axi_arvalid(s_axil_arvalid),
      .i_axi_arready(s_axil_arready),
      .i_axi_arprot ('0),

      .i_axi_rvalid(s_axil_rvalid),
      .i_axi_rready(s_axil_rready),
      .i_axi_rdata (s_axil_rdata),
      .i_axi_rresp (s_axil_rresp),

      .f_axi_rd_outstanding (),
      .f_axi_wr_outstanding (),
      .f_axi_awr_outstanding()
  );

  // Instantiate faxil_master for each subordinate
  for (genvar i = 0; i < NUM_S; i = i + 1) begin : g_faxil_manager
    faxil_master #(
        .C_AXI_DATA_WIDTH  (M_AXIL_DATA_WIDTH),
        .C_AXI_ADDR_WIDTH  (M_AXIL_ADDR_WIDTH),
        .F_AXI_MAXWAIT     (1),
        .F_AXI_MAXDELAY    (1),
        .F_AXI_MAXRSTALL   (0),
        .F_OPT_READ_ONLY   (0),
        .F_OPT_INITIAL     (0),
        .F_OPT_ASSUME_RESET(1)
    ) faxil_manager_i (
        .i_clk        (clk),
        .i_axi_reset_n(rst_n),

        // Write address channel
        .i_axi_awvalid(m_axil_awvalid[i]),
        .i_axi_awready(m_axil_awready[i]),
        .i_axi_awaddr (m_axil_awaddr[i]),
        .i_axi_awprot (3'b000),

        // Write data
        .i_axi_wready(m_axil_wready[i]),
        .i_axi_wdata (m_axil_wdata[i]),
        .i_axi_wstrb (m_axil_wstrb[i]),
        .i_axi_wvalid(m_axil_wvalid[i]),

        // Write response
        .i_axi_bresp (m_axil_bresp[i]),
        .i_axi_bvalid(m_axil_bvalid[i]),
        .i_axi_bready(m_axil_bready[i]),

        // Read address
        .i_axi_arvalid(m_axil_arvalid[i]),
        .i_axi_arready(m_axil_arready[i]),
        .i_axi_araddr (m_axil_araddr[i]),
        .i_axi_arprot (3'b000),

        // Read data return
        .i_axi_rvalid(m_axil_rvalid[i]),
        .i_axi_rready(m_axil_rready[i]),
        .i_axi_rdata (m_axil_rdata[i]),
        .i_axi_rresp (m_axil_rresp[i]),

        // Formal check variables
        .f_axi_rd_outstanding (),
        .f_axi_wr_outstanding (),
        .f_axi_awr_outstanding()
    );
  end

`endif
`endif

endmodule
`endif
