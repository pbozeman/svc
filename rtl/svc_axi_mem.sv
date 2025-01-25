`ifndef SVC_AXI_MEM_SV
`define SVC_AXI_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// AXI backed by internal memory, primarily intended for testing.
//
// If this gets used for more than casual testing, it might be nice to pass in
// the memory interface so that the instantiating module can ensure that
// vendor specific BRAM IP gets inferred/synthesized correctly.
//
module svc_axi_mem #(
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_awvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    output logic                      s_axi_awready,
    input  logic                      s_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_wready,
    output logic                      s_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,
    input  logic                      s_axi_bready,

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
    input  logic                      s_axi_rready
);
  parameter LSB = $clog2(AXI_DATA_WIDTH) - 3;

  parameter MEM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB;
  parameter WORD_WIDTH = AXI_STRB_WIDTH;
  parameter WORD_SIZE = AXI_DATA_WIDTH / WORD_WIDTH;

  logic [AXI_DATA_WIDTH-1:0] mem         [(1 << MEM_ADDR_WIDTH)-1:0];

  logic                      mem_wr_en;
  logic [MEM_ADDR_WIDTH-1:0] mem_wr_addr;

  logic                      mem_rd_en;
  logic [MEM_ADDR_WIDTH-1:0] mem_rd_addr;

  typedef enum {
    WRITE_STATE_IDLE,
    WRITE_STATE_BURST,
    WRITE_STATE_RESP
  } write_state_t;

  typedef enum {
    READ_STATE_IDLE,
    READ_STATE_BURST
  } read_state_t;

  //
  // Write signals
  //
  write_state_t                      write_state;
  write_state_t                      write_state_next;

  logic                              s_axi_awready_next;
  logic                              s_axi_wready_next;
  logic                              s_axi_bvalid_next;
  logic         [  AXI_ID_WIDTH-1:0] s_axi_bid_next;

  logic         [  AXI_ID_WIDTH-1:0] w_id;
  logic         [  AXI_ID_WIDTH-1:0] w_id_next;

  logic         [AXI_ADDR_WIDTH-1:0] w_addr;
  logic         [AXI_ADDR_WIDTH-1:0] w_addr_next;

  logic         [               2:0] w_size;
  logic         [               2:0] w_size_next;

  logic         [               1:0] w_burst;
  logic         [               1:0] w_burst_next;

  //
  // Read signals
  //
  read_state_t                       read_state;
  read_state_t                       read_state_next;

  logic                              s_axi_arready_next;
  logic                              s_axi_rvalid_next;
  logic         [  AXI_ID_WIDTH-1:0] s_axi_rid_next;
  logic                              s_axi_rlast_next;

  logic         [  AXI_ID_WIDTH-1:0] r_id;
  logic         [  AXI_ID_WIDTH-1:0] r_id_next;

  logic         [AXI_ADDR_WIDTH-1:0] r_addr;
  logic         [AXI_ADDR_WIDTH-1:0] r_addr_next;

  logic         [               7:0] r_len;
  logic         [               7:0] r_len_next;

  logic         [               2:0] r_size;
  logic         [               2:0] r_size_next;

  logic         [               1:0] r_burst;
  logic         [               1:0] r_burst_next;


  //-------------------------------------------------------------------------
  //
  // Write state machine
  //
  //-------------------------------------------------------------------------

  always @(*) begin
    write_state_next   = write_state;

    w_id_next          = w_id;
    w_addr_next        = w_addr;
    w_size_next        = w_size;
    w_burst_next       = w_burst;

    s_axi_awready_next = s_axi_awready;
    s_axi_wready_next  = s_axi_wready;

    s_axi_bid_next     = s_axi_bid;
    s_axi_bvalid_next  = s_axi_bvalid && !s_axi_bready;

    mem_wr_en          = 1'b0;

    case (write_state)
      WRITE_STATE_IDLE: begin
        if (s_axi_awvalid && s_axi_awready) begin
          write_state_next   = WRITE_STATE_BURST;
          s_axi_awready_next = 1'b0;
          s_axi_wready_next  = 1'b1;

          w_id_next          = s_axi_awid;
          w_addr_next        = s_axi_awaddr;
          w_size_next        = s_axi_awsize;
          w_burst_next       = s_axi_awburst;

          // and also do the first write, if possible, to avoid a cycle of latency
          // TODO: this currently won't trigger because wready will be low.
          // Bring ready high in the same cycle as awvalid && awready and this
          // will be triggered again. (It had to be blocked because we can't
          // have valid/ready going through before the addr has been accepted
          // or it vastly complicates state management because we have to defer
          // the write.)
          if (s_axi_wvalid && s_axi_wready) begin
            mem_wr_en   = 1'b1;
            mem_wr_addr = s_axi_awaddr[AXI_ADDR_WIDTH-1:LSB];

            if (s_axi_awburst != 2'b00) begin
              w_addr_next = s_axi_awaddr + (1 << s_axi_awsize);
            end

            if (s_axi_wlast) begin
              if (!s_axi_bvalid || s_axi_bready) begin
                write_state_next   = WRITE_STATE_IDLE;
                s_axi_awready_next = 1'b1;
                s_axi_bvalid_next  = 1'b1;
                s_axi_bid_next     = s_axi_awid;
              end else begin
                write_state_next  = WRITE_STATE_RESP;
                s_axi_wready_next = 1'b0;
              end
            end
          end
        end
      end

      WRITE_STATE_BURST: begin
        s_axi_wready_next = 1'b1;

        if (s_axi_wvalid && s_axi_wready) begin
          mem_wr_en   = 1'b1;
          mem_wr_addr = w_addr[AXI_ADDR_WIDTH-1:LSB];

          if (w_burst != 2'b00) begin
            w_addr_next = w_addr + (1 << w_size);
          end

          if (s_axi_wlast) begin
            if (!s_axi_bvalid || s_axi_bready) begin
              write_state_next   = WRITE_STATE_IDLE;
              s_axi_awready_next = 1'b1;
              s_axi_wready_next  = 1'b0;
              s_axi_bvalid_next  = 1'b1;
              s_axi_bid_next     = w_id;
            end else begin
              write_state_next  = WRITE_STATE_RESP;
              s_axi_wready_next = 1'b0;
            end
          end
        end
      end

      WRITE_STATE_RESP: begin
        if (s_axi_bvalid && s_axi_bready) begin
          write_state_next   = WRITE_STATE_IDLE;
          s_axi_awready_next = 1'b1;
          s_axi_wready_next  = 1'b0;
          s_axi_bvalid_next  = 1'b1;
          s_axi_bid_next     = w_id;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      write_state   <= WRITE_STATE_IDLE;
      s_axi_awready <= 1'b1;
      s_axi_wready  <= 1'b0;
      s_axi_bvalid  <= 1'b0;
    end else begin
      write_state   <= write_state_next;
      s_axi_awready <= s_axi_awready_next;
      s_axi_wready  <= s_axi_wready_next;
      s_axi_bvalid  <= s_axi_bvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    w_id        <= w_id_next;
    w_addr      <= w_addr_next;
    w_size      <= w_size_next;
    w_burst     <= w_burst_next;

    s_axi_bid   <= s_axi_bid_next;
    s_axi_bresp <= 2'b00;
  end

  always_ff @(posedge clk) begin
    for (int i = 0; i < WORD_WIDTH; i = i + 1) begin
      if (mem_wr_en & s_axi_wstrb[i]) begin
        mem[mem_wr_addr][WORD_SIZE*i+:WORD_SIZE] <=
            s_axi_wdata[WORD_SIZE*i+:WORD_SIZE];
      end
    end
  end

  //-------------------------------------------------------------------------
  //
  // Read state machine
  //
  //-------------------------------------------------------------------------

  always @(*) begin
    read_state_next    = read_state;

    r_id_next          = r_id;
    r_addr_next        = r_addr;
    r_len_next         = r_len;
    r_size_next        = r_size;
    r_burst_next       = r_burst;

    s_axi_rid_next     = s_axi_rid;
    s_axi_arready_next = s_axi_arready;
    s_axi_rvalid_next  = s_axi_rvalid && !s_axi_rready;
    s_axi_rlast_next   = s_axi_rlast;

    mem_rd_en          = 1'b0;
    mem_rd_addr        = 0;

    case (read_state)
      READ_STATE_IDLE: begin
        if (s_axi_arvalid && s_axi_arready) begin
          read_state_next    = READ_STATE_BURST;
          s_axi_arready_next = 1'b0;

          r_id_next          = s_axi_arid;
          r_addr_next        = s_axi_araddr;
          r_len_next         = s_axi_arlen;
          r_size_next        = s_axi_arsize;
          r_burst_next       = s_axi_arburst;

          // and also do the first read, if possible, to avoid a cycle of latency
          if (!s_axi_rvalid || s_axi_rready) begin
            mem_rd_en         = 1'b1;
            mem_rd_addr       = s_axi_araddr[AXI_ADDR_WIDTH-1:LSB];

            s_axi_rvalid_next = 1'b1;
            s_axi_rid_next    = s_axi_arid;
            s_axi_rlast_next  = s_axi_arlen == 0;

            if (s_axi_arburst != 2'b00) begin
              r_addr_next = s_axi_araddr + (1 << s_axi_arsize);
            end

            r_len_next = s_axi_arlen - 1;
            if (s_axi_arlen == 0) begin
              read_state_next    = READ_STATE_IDLE;
              s_axi_arready_next = 1'b1;
            end
          end
        end
      end

      READ_STATE_BURST: begin
        if (!s_axi_rvalid || s_axi_rready) begin
          mem_rd_en         = 1'b1;
          mem_rd_addr       = r_addr[AXI_ADDR_WIDTH-1:LSB];

          s_axi_rvalid_next = 1'b1;
          s_axi_rid_next    = r_id;
          s_axi_rlast_next  = r_len == 0;

          if (r_burst != 2'b00) begin
            r_addr_next = r_addr + (1 << r_size);
          end

          r_len_next = r_len - 1;
          if (r_len == 0) begin
            read_state_next    = READ_STATE_IDLE;
            s_axi_arready_next = 1'b1;
          end
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      read_state    <= READ_STATE_IDLE;
      s_axi_arready <= 1'b1;
      s_axi_rvalid  <= 1'b0;
    end else begin
      read_state    <= read_state_next;
      s_axi_arready <= s_axi_arready_next;
      s_axi_rvalid  <= s_axi_rvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    r_id        <= r_id_next;
    r_addr      <= r_addr_next;
    r_len       <= r_len_next;
    r_size      <= r_size_next;
    r_burst     <= r_burst_next;

    s_axi_rid   <= s_axi_rid_next;
    s_axi_rresp <= 2'b00;
    s_axi_rlast <= s_axi_rlast_next;
  end

  always_ff @(posedge clk) begin
    if (mem_rd_en) begin
      s_axi_rdata <= mem[mem_rd_addr];
    end
  end

  `SVC_UNUSED(s_axi_awlen);

`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_AXI_MEM
  logic [8:0] f_axi_wr_pending;

  logic       f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);

    // FIXME: this over constrains the state space as this can actually happen
    // in real usage, but is necessary for faxi_slave.v. See faxi_slave.v:664
    if (f_axi_wr_pending > 0) begin
      assume (!s_axi_awready);
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
      .i_axi_awready(s_axi_awready),
      .i_axi_awid   (s_axi_awid),
      .i_axi_awaddr (s_axi_awaddr),
      .i_axi_awlen  (s_axi_awlen),
      .i_axi_awsize (s_axi_awsize),
      .i_axi_awburst(s_axi_awburst),
      .i_axi_awlock (0),
      .i_axi_awcache(0),
      .i_axi_awprot (0),
      .i_axi_awqos  (0),
      .i_axi_awvalid(s_axi_awvalid),

      // Write data
      .i_axi_wready(s_axi_wready),
      .i_axi_wdata (s_axi_wdata),
      .i_axi_wstrb (s_axi_wstrb),
      .i_axi_wlast (s_axi_wlast),
      .i_axi_wvalid(s_axi_wvalid),

      // Write return response
      .i_axi_bid   (s_axi_bid),
      .i_axi_bresp (s_axi_bresp),
      .i_axi_bvalid(s_axi_bvalid),
      .i_axi_bready(s_axi_bready),

      // Read address
      .i_axi_arready(s_axi_arready),
      .i_axi_arid   (s_axi_arid),
      .i_axi_araddr (s_axi_araddr),
      .i_axi_arlen  (s_axi_arlen),
      .i_axi_arsize (s_axi_arsize),
      .i_axi_arburst(s_axi_arburst),
      .i_axi_arlock (0),
      .i_axi_arcache(0),
      .i_axi_arprot (0),
      .i_axi_arqos  (0),
      .i_axi_arvalid(s_axi_arvalid),

      // Read response
      .i_axi_rid   (s_axi_rid),
      .i_axi_rresp (s_axi_rresp),
      .i_axi_rvalid(s_axi_rvalid),
      .i_axi_rdata (s_axi_rdata),
      .i_axi_rlast (s_axi_rlast),
      .i_axi_rready(s_axi_rready),

      .f_axi_awr_nbursts   (),
      .f_axi_wr_pending    (f_axi_wr_pending),
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

`endif
`endif
`endif

endmodule
`endif
