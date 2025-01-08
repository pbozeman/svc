`ifndef SVC_AXIL_SRAM_IF_SV
`define SVC_AXIL_SRAM_IF_SV

`include "svc.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// This is a wrapper to convert byte based AXI-Lite to an SRAM interface.
// It arbitrates between reads and writes, as the SRAM can only
// do 1 at a time. It also converts the addresses to be word rather than byte
// based. rresp and bresp are always marked as success.
//
// Reads and writes are passed to the SRAM via small fifos to absorb
// backpressure since it takes 2 clocks per operation to the sram. Results
// are similarly buffered to avoid dropping results from ready signal
// propagation through the pipeline.
//
// Note: the fifos added a cycle of latency to both the incoming
// and outgoing sides, i.e. we're now at 2 cycles of latency for this module,
// and when used with the real sram chips, they will add 2 more. Granted, this
// module is capable of an io every clock, but still, it might be nice
// to look into some way of reducing this. It looks like "pipelined skid
// buffers" (basically an n-deep skid buffer) might do the trick, but at first
// glance it isn't clear if they provide zero latency like a normal skidbuf,
// and even if they do, if the overhead is worth the latency drop. For now,
// this little bit of extra latency is fine as the pipeline performance of
// this module is great since it provides 100% throughput.
module svc_axil_sram_if #(
    parameter AXIL_ADDR_WIDTH = 4,
    parameter AXIL_DATA_WIDTH = 16,
    parameter AXIL_STRB_WIDTH = (AXIL_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXIL_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXIL_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXIL_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXIL_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI-Lite subordinate interface
    //
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [                1:0] s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    //
    // SRAM interface
    //
    output logic                       sram_cmd_valid,
    input  logic                       sram_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    output logic                       sram_cmd_wr_en,
    output logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    input  logic                       sram_resp_rd_valid,
    output logic                       sram_resp_rd_ready,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data
);
  localparam FIFO_ADDR_WIDTH = 2;

  localparam FIFO_AR_WIDTH = SRAM_ADDR_WIDTH;
  localparam FIFO_R_WIDTH = SRAM_DATA_WIDTH;

  localparam FIFO_AW_WIDTH = SRAM_ADDR_WIDTH;
  localparam FIFO_W_WIDTH = SRAM_DATA_WIDTH + SRAM_STRB_WIDTH;

  //
  // ar channel fifo signals
  //
  logic                       fifo_ar_w_inc;
  logic [  FIFO_AR_WIDTH-1:0] fifo_ar_w_data;
  logic                       fifo_ar_w_half_full;

  logic                       fifo_ar_r_inc;
  logic                       fifo_ar_r_empty;
  logic [  FIFO_AR_WIDTH-1:0] fifo_ar_r_data;

  //
  // r channel fifo signals
  //
  logic                       fifo_r_w_inc;
  logic [   FIFO_R_WIDTH-1:0] fifo_r_w_data;
  logic                       fifo_r_w_half_full;

  logic                       fifo_r_r_inc;
  logic                       fifo_r_r_empty;
  logic [   FIFO_R_WIDTH-1:0] fifo_r_r_data;

  //
  // aw channel fifo signals
  //
  logic                       fifo_aw_w_inc;
  logic [  FIFO_AW_WIDTH-1:0] fifo_aw_w_data;
  logic                       fifo_aw_w_half_full;

  logic                       fifo_aw_r_inc;
  logic                       fifo_aw_r_empty;
  logic [  FIFO_AW_WIDTH-1:0] fifo_aw_r_data;

  //
  // w channel fifo signals
  //
  logic                       fifo_w_w_inc;
  logic [   FIFO_W_WIDTH-1:0] fifo_w_w_data;
  logic                       fifo_w_w_half_full;

  logic                       fifo_w_r_inc;
  logic                       fifo_w_r_empty;
  logic [   FIFO_W_WIDTH-1:0] fifo_w_r_data;

  //
  // arbiter signals
  //
  logic                       pri_rd;
  logic                       pri_rd_next;
  logic                       rd_ok;
  logic                       wr_ok;

  logic                       sram_cmd_valid_next;
  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr_next;
  logic                       sram_cmd_wr_en_next;
  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data_next;
  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb_next;

  //
  // ar channel
  //
  assign fifo_ar_w_inc  = s_axil_arvalid && s_axil_arready;
  assign fifo_ar_w_data = s_axil_araddr[AXIL_ADDR_WIDTH-1:LSB];
  assign s_axil_arready = !(fifo_ar_w_half_full || fifo_r_w_half_full);

  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(FIFO_AR_WIDTH)
  ) svc_sync_fifo_ar_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (fifo_ar_w_inc),
      .w_data     (fifo_ar_w_data),
      .w_full     (),
      .w_half_full(fifo_ar_w_half_full),
      .r_inc      (fifo_ar_r_inc),
      .r_empty    (fifo_ar_r_empty),
      .r_data     (fifo_ar_r_data)
  );

  //
  // r channel
  //
  assign fifo_r_w_inc  = sram_resp_rd_valid && sram_resp_rd_ready;
  assign fifo_r_w_data = sram_resp_rd_data;

  assign s_axil_rvalid = !fifo_r_r_empty;
  assign s_axil_rdata  = fifo_r_r_data;
  assign s_axil_rresp  = 2'b00;
  assign fifo_r_r_inc  = s_axil_rvalid && s_axil_rready;

  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(FIFO_R_WIDTH)
  ) svc_sync_fifo_r_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (fifo_r_w_inc),
      .w_data     (fifo_r_w_data),
      .w_full     (),
      .w_half_full(fifo_r_w_half_full),
      .r_inc      (fifo_r_r_inc),
      .r_empty    (fifo_r_r_empty),
      .r_data     (fifo_r_r_data)
  );

  //
  // aw channel
  //
  assign fifo_aw_w_inc  = s_axil_awvalid && s_axil_awready;
  assign fifo_aw_w_data = s_axil_awaddr[AXIL_ADDR_WIDTH-1:LSB];
  assign s_axil_awready = !fifo_aw_w_half_full;

  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(FIFO_AW_WIDTH)
  ) svc_sync_fifo_aw_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (fifo_aw_w_inc),
      .w_data     (fifo_aw_w_data),
      .w_full     (),
      .w_half_full(fifo_aw_w_half_full),
      .r_inc      (fifo_aw_r_inc),
      .r_empty    (fifo_aw_r_empty),
      .r_data     (fifo_aw_r_data)
  );

  //
  // w channel
  //
  assign fifo_w_w_inc = s_axil_wvalid && s_axil_wready;
  assign fifo_w_w_data = {s_axil_wdata, s_axil_wstrb};
  assign s_axil_wready =
      !(fifo_w_w_half_full || (s_axil_bvalid && !s_axil_bready));

  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(FIFO_W_WIDTH)
  ) svc_sync_fifo_w_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (fifo_w_w_inc),
      .w_data     (fifo_w_w_data),
      .w_full     (),
      .w_half_full(fifo_w_w_half_full),
      .r_inc      (fifo_w_r_inc),
      .r_empty    (fifo_w_r_empty),
      .r_data     (fifo_w_r_data)
  );

  //
  // b channel
  //
  logic [FIFO_ADDR_WIDTH-1:0] bcnt;
  logic [FIFO_ADDR_WIDTH-1:0] bcnt_next;
  assign s_axil_bresp = 2'b00;

  always_comb begin
    case ({
      (sram_cmd_valid && sram_cmd_ready && sram_cmd_wr_en),
      (s_axil_bvalid && s_axil_bready)
    })
      2'b01: begin
        bcnt_next = bcnt - 1;
      end

      2'b10: begin
        bcnt_next = bcnt + 1;
      end

      2'b00, 2'b11: begin
        bcnt_next = bcnt;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      bcnt          <= 0;
      s_axil_bvalid <= 1'b0;
    end else begin
      bcnt          <= bcnt_next;
      s_axil_bvalid <= bcnt_next > 0;
    end
  end

  //
  // arbiter
  //
  assign rd_ok = !fifo_ar_r_empty && !fifo_r_w_half_full;
  assign wr_ok = (!fifo_aw_r_empty && !fifo_w_r_empty &&
                  (bcnt < (1 << (FIFO_ADDR_WIDTH - 1))));

  always_comb begin
    sram_cmd_valid_next   = sram_cmd_valid && !sram_cmd_ready;
    sram_cmd_addr_next    = sram_cmd_addr;
    sram_cmd_wr_en_next   = sram_cmd_wr_en;
    sram_cmd_wr_data_next = sram_cmd_wr_data;
    sram_cmd_wr_strb_next = sram_cmd_wr_strb;
    fifo_ar_r_inc         = 1'b0;
    fifo_aw_r_inc         = 1'b0;
    fifo_w_r_inc          = 1'b0;
    pri_rd_next           = pri_rd;

    if (!sram_cmd_valid || sram_cmd_ready) begin
      if (pri_rd) begin
        if (rd_ok) begin
          sram_cmd_valid_next = 1'b1;
          sram_cmd_addr_next  = fifo_ar_r_data;
          sram_cmd_wr_en_next = 1'b0;
          fifo_ar_r_inc       = 1'b1;
          pri_rd_next         = 1'b0;
        end else if (wr_ok) begin
          sram_cmd_valid_next                            = 1'b1;
          sram_cmd_addr_next                             = fifo_aw_r_data;
          sram_cmd_wr_en_next                            = 1'b1;
          {sram_cmd_wr_data_next, sram_cmd_wr_strb_next} = fifo_w_r_data;
          fifo_aw_r_inc                                  = 1'b1;
          fifo_w_r_inc                                   = 1'b1;
          pri_rd_next                                    = 1'b1;
        end
      end else begin
        if (wr_ok) begin
          sram_cmd_valid_next                            = 1'b1;
          sram_cmd_addr_next                             = fifo_aw_r_data;
          sram_cmd_wr_en_next                            = 1'b1;
          {sram_cmd_wr_data_next, sram_cmd_wr_strb_next} = fifo_w_r_data;
          fifo_aw_r_inc                                  = 1'b1;
          fifo_w_r_inc                                   = 1'b1;
          pri_rd_next                                    = 1'b1;
        end else if (rd_ok) begin
          sram_cmd_valid_next = 1'b1;
          sram_cmd_addr_next  = fifo_ar_r_data;
          sram_cmd_wr_en_next = 1'b0;
          fifo_ar_r_inc       = 1'b1;
          pri_rd_next         = 1'b0;
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      sram_cmd_valid <= 1'b0;
      pri_rd         <= 1'b0;
    end else begin
      pri_rd           <= pri_rd_next;
      sram_cmd_valid   <= sram_cmd_valid_next;
      sram_cmd_addr    <= sram_cmd_addr_next;
      sram_cmd_wr_en   <= sram_cmd_wr_en_next;
      sram_cmd_wr_data <= sram_cmd_wr_data_next;
      sram_cmd_wr_strb <= sram_cmd_wr_strb_next;
    end
  end

  assign sram_resp_rd_ready = !fifo_r_w_half_full;

  `SVC_UNUSED({s_axil_awaddr[3:0], s_axil_araddr[3:0]});

`ifdef FORMAL
  // the number of bits necessary to count the maximum number
  // of items in flight.
  localparam F_LGDEPTH = 4;

  // the svc modules don't init all values pre-reset
  localparam F_OPT_INITIAL = 0;

  // Since the sram can not run read and write at the same time,
  // the stall must be less than the delay, or else a stall on one channel can
  // cause max delay to be hit on the other, which would be the expected
  // behavior. (12 was the default for both, so give a small amount of
  // of breathing room)
  localparam F_AXI_MAXRSTALL = 8;
  localparam F_AXI_MAXDELAY = 12;

  // verilator lint_off: UNUSEDSIGNAL
  wire  [F_LGDEPTH-1:0] f_axil_rd_outstanding;
  wire  [F_LGDEPTH-1:0] f_axil_wr_outstanding;
  wire  [F_LGDEPTH-1:0] f_axil_awr_outstanding;
  // verilator lint_on: UNUSEDSIGNAL

  logic                 f_past_valid;

  initial f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  faxil_slave #(
      .C_AXI_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXIL_DATA_WIDTH),
      .F_LGDEPTH       (F_LGDEPTH),
      .F_OPT_INITIAL   (F_OPT_INITIAL),
      .F_AXI_MAXRSTALL (F_AXI_MAXRSTALL),
      .F_AXI_MAXDELAY  (F_AXI_MAXDELAY)
  ) faxil_i (
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

      .f_axi_rd_outstanding (f_axil_rd_outstanding),
      .f_axi_wr_outstanding (f_axil_wr_outstanding),
      .f_axi_awr_outstanding(f_axil_awr_outstanding)
  );

  // verilator lint_off: ASSIGNIN
  // allowing these assignments via ASSIGNIN is a bit janky, but otherwise, I need to
  // change the model to be assume rather than assign based, and it's already
  // used in normal unit tbs. This lets use use if for both use cases, but
  // maybe come back and address this.
  svc_model_sram_if #(
      .SRAM_ADDR_WIDTH     (SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH     (SRAM_DATA_WIDTH),
      .UNITIALIZED_READS_OK(1)
  ) svc_model_sram_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid   (sram_cmd_valid),
      .sram_cmd_ready   (sram_cmd_ready),
      .sram_cmd_addr    (sram_cmd_addr),
      .sram_cmd_meta    (),
      .sram_cmd_last    (),
      .sram_cmd_wr_en   (sram_cmd_wr_en),
      .sram_cmd_wr_data (sram_cmd_wr_data),
      .sram_cmd_wr_strb (sram_cmd_wr_strb),
      .sram_resp_valid  (sram_resp_rd_valid),
      .sram_resp_ready  (sram_resp_rd_ready),
      .sram_resp_rd_data(sram_resp_rd_data),
      .sram_resp_meta   (),
      .sram_resp_last   ()
  );
  // verilator lint_on: ASSIGNIN

  // ensure we can do 5 io ops in a row, 1 every clock cycle.
  // Why 5? Because our fifos are set to a depth of 4.
  //
  // ensure we can get 5 write responses in a row, 1 every clock cycle
  always @(posedge clk) begin
    if ((f_past_valid) && (rst_n))
      c_write_per_clk :
      cover ((s_axil_bvalid && s_axil_bready) && ($past(
          (s_axil_bvalid && s_axil_bready), 1
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 2
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 3
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 4
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 5
      )));
  end

  // ensure we can do 5 read responses in a row, 1 every clock cycle
  always @(posedge clk) begin
    c_read_per_clk :
    cover ((s_axil_rvalid && s_axil_rready) && ($past(
        (s_axil_rvalid && s_axil_rready), 1
    )) && ($past(
        (s_axil_rvalid && s_axil_rready), 2
    )) && ($past(
        (s_axil_rvalid && s_axil_rready), 3
    )) && ($past(
        (s_axil_rvalid && s_axil_rready), 4
    )) && ($past(
        (s_axil_rvalid && s_axil_rready), 5
    )));
  end

  // Look into properties to use induction and an unbounded check
  //
  // This is going to be a bit of a pain as it is going to require counting
  // all the entries in the fifos.
  //
  // see
  //   https://zipcpu.com/blog/2020/03/08/easyaxil.html
  // and
  //   https://github.com/ZipCPU/wb2axip/blob/master/rtl/demoaxi.v
`endif

endmodule
`endif
