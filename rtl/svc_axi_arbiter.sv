`ifndef SVC_AXI_ARBITER_SV
`define SVC_AXI_ARBITER_SV

`include "svc.sv"
`include "svc_axi_arbiter_rd.sv"
`include "svc_axi_arbiter_wr.sv"

//
// AXI arbiter from N managers to 1 subordinate.
//
module svc_axi_arbiter #(
    parameter NUM_M          = 2,
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4,
    parameter M_AXI_ID_WIDTH = AXI_ID_WIDTH + $clog2(NUM_M)
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface for N managers
    //
    input  logic [NUM_M-1:0]                     s_axi_awvalid,
    input  logic [NUM_M-1:0][AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [NUM_M-1:0][               7:0] s_axi_awlen,
    input  logic [NUM_M-1:0][               2:0] s_axi_awsize,
    input  logic [NUM_M-1:0][               1:0] s_axi_awburst,
    output logic [NUM_M-1:0]                     s_axi_awready,
    input  logic [NUM_M-1:0]                     s_axi_wvalid,
    input  logic [NUM_M-1:0][AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [NUM_M-1:0][AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic [NUM_M-1:0]                     s_axi_wlast,
    output logic [NUM_M-1:0]                     s_axi_wready,
    output logic [NUM_M-1:0]                     s_axi_bvalid,
    output logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [NUM_M-1:0][               1:0] s_axi_bresp,
    input  logic [NUM_M-1:0]                     s_axi_bready,

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
    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [M_AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,
    output logic                      m_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    input  logic                      m_axi_bvalid,
    input  logic [M_AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready,

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
  svc_axi_arbiter_wr #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_arbiter_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bready (s_axi_bready),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wlast  (m_axi_wlast),
      .m_axi_wready (m_axi_wready),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bid    (m_axi_bid),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bready (m_axi_bready)
  );

  svc_axi_arbiter_rd #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_arbiter_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arready(s_axi_arready),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),
      .s_axi_rready (s_axi_rready),

      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arid   (m_axi_arid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rready (m_axi_rready)
  );

`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_AXI_ARBITER
  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  logic [8:0] f_axi_wr_pending[NUM_M-1:0];

  for (genvar i = 0; i < NUM_M; i++) begin : gen_faxi_s
    always @(*) begin
      // FIXME: this over constrains the state space as this can actually happen
      // in real usage, but is necessary for faxi_slave.v. See faxi_slave.v:664
      if (f_axi_wr_pending[i] > 0) begin
        assume (!s_axi_awready[i]);
      end
    end

    faxi_slave #(
        .C_AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .C_AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .C_AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .F_AXI_MAXSTALL    (0),
        .F_AXI_MAXRSTALL   (3),
        .F_OPT_INITIAL     (0),
        .OPT_EXCLUSIVE     (0),
        .F_AXI_MAXDELAY    (0),
        .F_OPT_ASSUME_RESET(1)
    ) faxi_subordinate_i (
        .i_clk        (clk),
        .i_axi_reset_n(rst_n),

        // Write address
        .i_axi_awready(s_axi_awready[i]),
        .i_axi_awid   (s_axi_awid[i]),
        .i_axi_awaddr (s_axi_awaddr[i]),
        .i_axi_awlen  (s_axi_awlen[i]),
        .i_axi_awsize (s_axi_awsize[i]),
        .i_axi_awburst(s_axi_awburst[i]),
        .i_axi_awlock (0),
        .i_axi_awcache(0),
        .i_axi_awprot (0),
        .i_axi_awqos  (0),
        .i_axi_awvalid(s_axi_awvalid[i]),

        // Write data
        .i_axi_wready(s_axi_wready[i]),
        .i_axi_wdata (s_axi_wdata[i]),
        .i_axi_wstrb (s_axi_wstrb[i]),
        .i_axi_wlast (s_axi_wlast[i]),
        .i_axi_wvalid(s_axi_wvalid[i]),

        // Write return response
        .i_axi_bid   (s_axi_bid[i]),
        .i_axi_bresp (s_axi_bresp[i]),
        .i_axi_bvalid(s_axi_bvalid[i]),
        .i_axi_bready(s_axi_bready[i]),

        // Read address
        .i_axi_arready(s_axi_arready[i]),
        .i_axi_arid   (s_axi_arid[i]),
        .i_axi_araddr (s_axi_araddr[i]),
        .i_axi_arlen  (s_axi_arlen[i]),
        .i_axi_arsize (s_axi_arsize[i]),
        .i_axi_arburst(s_axi_arburst[i]),
        .i_axi_arlock (0),
        .i_axi_arcache(0),
        .i_axi_arprot (0),
        .i_axi_arqos  (0),
        .i_axi_arvalid(s_axi_arvalid[i]),

        // Read response
        .i_axi_rid   (s_axi_rid[i]),
        .i_axi_rresp (s_axi_rresp[i]),
        .i_axi_rvalid(s_axi_rvalid[i]),
        .i_axi_rdata (s_axi_rdata[i]),
        .i_axi_rlast (s_axi_rlast[i]),
        .i_axi_rready(s_axi_rready[i]),

        .f_axi_awr_nbursts   (),
        .f_axi_wr_pending    (f_axi_wr_pending[i]),
        .f_axi_rd_nbursts    (),
        .f_axi_rd_outstanding(),

        // Write burst properties
        .f_axi_wr_checkid  (),
        .f_axi_wr_ckvalid  (),
        .f_axi_wrid_nbursts(),
        .f_axi_wr_addr     (),
        .f_axi_wr_incr     (),
        .f_axi_wr_burst    (),
        .f_axi_wr_size     (),
        .f_axi_wr_len      (),
        .f_axi_wr_lockd    (),

        // Read properties
        .f_axi_rd_checkid(),
        .f_axi_rd_ckvalid(),
        .f_axi_rd_cklen  (),
        .f_axi_rd_ckaddr (),
        .f_axi_rd_ckincr (),
        .f_axi_rd_ckburst(),
        .f_axi_rd_cksize (),
        .f_axi_rd_ckarlen(),
        .f_axi_rd_cklockd(),

        .f_axi_rdid_nbursts          (),
        .f_axi_rdid_outstanding      (),
        .f_axi_rdid_ckign_nbursts    (),
        .f_axi_rdid_ckign_outstanding(),

        // Exclusive access handling
        .f_axi_ex_state              (),
        .f_axi_ex_checklock          (),
        .f_axi_rdid_bursts_to_lock   (),
        .f_axi_wrid_bursts_to_exwrite(),

        .f_axi_exreq_addr  (),
        .f_axi_exreq_len   (),
        .f_axi_exreq_burst (),
        .f_axi_exreq_size  (),
        .f_axi_exreq_return(),

        .i_active_lock (0),
        .i_exlock_addr (),
        .i_exlock_len  (),
        .i_exlock_burst(),
        .i_exlock_size ()
    );
  end

`ifndef VERILATOR
  // See note in svc_axi_stripe about why we only use axi mem and not the
  // zipcpu faxi_m.
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (M_AXI_ID_WIDTH)
  ) svc_axi_mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awready(m_axi_awready),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bready (m_axi_bready),

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),
      .s_axi_rready (m_axi_rready)
  );
`endif

  //
  // Cover statement showing full throughput axi arbiter.
  //

  // verilator lint_off: UNDRIVEN
  logic [AXI_ID_WIDTH-1:0] f_some_id;
  // verilator lint_on: UNDRIVEN
  // verilog_format: off
  always @(posedge clk) begin
    assume($stable(f_some_id));
    if ((f_past_valid) && (rst_n)) begin
      c_beat_per_clk :
      cover ((s_axi_rready[0] && s_axi_rvalid[0] &&
              s_axi_rid[0] == f_some_id && s_axi_rlast[0]) &&
        $past(s_axi_rready[0] && s_axi_rvalid[0], 1) &&
        $past(s_axi_rready[0] && s_axi_rvalid[0], 2) &&
        $past(s_axi_rready[0] && s_axi_rvalid[0], 3) &&
        $past(s_axi_rready[0] && s_axi_rvalid[0], 4) &&
        $past(s_axi_rready[0] && s_axi_rvalid[0], 5) &&
        $past(s_axi_arvalid[0] && s_axi_arready[0] &&
              s_axi_arlen[0] == 5 && s_axi_arburst[0] == 2'b01 &&
              s_axi_arid[0] == f_some_id, 5));
    end
  end
  // verilog_format: on
`endif

`endif
`endif

endmodule
`endif
