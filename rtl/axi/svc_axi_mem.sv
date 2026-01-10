`ifndef SVC_AXI_MEM_SV
`define SVC_AXI_MEM_SV

`include "svc.sv"
`include "svc_skidbuf.sv"
`include "svc_unused.sv"

`ifndef FORMAL
`include "svc_readmemh.sv"
`endif

//
// AXI backed by internal memory, primarily intended for testing.
//
// If this gets used for more than casual testing, it might be nice to pass in
// the memory interface so that the instantiating module can ensure that
// vendor specific BRAM IP gets inferred/synthesized correctly.
//
// The optional INIT_FILE parameter specifies a hex file for memory
// initialization. The file should have one hex value per line matching
// the AXI_DATA_WIDTH (e.g., 32 hex chars per line for 128-bit data).
//
module svc_axi_mem #(
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter INIT_FILE = ""
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
  localparam AW = AXI_ADDR_WIDTH;
  localparam DW = AXI_DATA_WIDTH;
  localparam IW = AXI_ID_WIDTH;
  localparam STRBW = AXI_STRB_WIDTH;

  localparam LSB = $clog2(DW) - 3;

  localparam MEM_ADDR_WIDTH = AW - LSB;
  localparam WORD_WIDTH = STRBW;
  localparam WORD_SIZE = DW / WORD_WIDTH;

  logic [AXI_DATA_WIDTH-1:0] mem[(1 << MEM_ADDR_WIDTH)-1:0];

  //
  // Initialize memory from hex file
  //
`ifndef FORMAL
  initial begin : init_block
`ifndef SYNTHESIS
    int word_count;

    // Zero initialize
    for (int i = 0; i < (1 << MEM_ADDR_WIDTH); i = i + 1) begin
      mem[i] = {DW{1'b0}};
    end

    if (INIT_FILE != "") begin
      if (DW >= 32) begin
        // Hex file contains 32-bit words, pack into AXI_DATA_WIDTH entries.
        // temp_mem holds (AXI_DATA_WIDTH/32) times as many 32-bit words.
        // Use max(DW/32, 1) to avoid zero-size array when DW < 32
        // (declaration elaborates regardless of runtime condition).
        logic [31:0] temp_mem[(1<<MEM_ADDR_WIDTH)*((DW >= 32) ? (DW/32) : 1)];

        word_count = svc_readmemh_count(INIT_FILE);
        if (word_count > 0) begin
          localparam int WORDS_PER_ENTRY = DW / 32;

          $readmemh(INIT_FILE, temp_mem, 0, word_count - 1);
          // Copy all words, including remainder when word_count is not
          // a multiple of WORDS_PER_ENTRY
          for (int i = 0; i < word_count; i++) begin
            // verilator lint_off SELRANGE
            mem[i/WORDS_PER_ENTRY][(i%WORDS_PER_ENTRY)*32+:32] = temp_mem[i];
            // verilator lint_on SELRANGE
          end
        end
      end else begin
        // For narrow memories (< 32 bits), use direct $readmemh
        $readmemh(INIT_FILE, mem);
      end
    end
`else
    if (INIT_FILE != "") begin
      // Synthesis: use direct $readmemh (expects matching data width)
      $readmemh(INIT_FILE, mem);
    end
`endif
  end
`endif

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
  write_state_t             write_state;
  write_state_t             write_state_next;

  logic                     sb_s_awvalid;
  logic         [   AW-1:0] sb_s_awaddr;
  logic         [   IW-1:0] sb_s_awid;
  logic         [      2:0] sb_s_awsize;
  logic         [      1:0] sb_s_awburst;
  logic                     sb_s_awready;

  logic                     sb_s_wvalid;
  logic         [   DW-1:0] sb_s_wdata;
  logic         [STRBW-1:0] sb_s_wstrb;
  logic                     sb_s_wlast;
  logic                     sb_s_wready;

  logic                     s_axi_bvalid_next;
  logic         [   IW-1:0] s_axi_bid_next;

  logic         [   IW-1:0] w_id;
  logic         [   IW-1:0] w_id_next;

  logic         [   AW-1:0] w_addr;
  logic         [   AW-1:0] w_addr_next;

  logic         [      2:0] w_size;
  logic         [      2:0] w_size_next;

  logic         [      1:0] w_burst;
  logic         [      1:0] w_burst_next;

  //
  // Read signals
  //
  read_state_t              read_state;
  read_state_t              read_state_next;

  logic                     s_axi_arready_next;
  logic                     s_axi_rvalid_next;
  logic         [   IW-1:0] s_axi_rid_next;
  logic                     s_axi_rlast_next;

  logic         [   IW-1:0] r_id;
  logic         [   IW-1:0] r_id_next;

  logic         [   AW-1:0] r_addr;
  logic         [   AW-1:0] r_addr_next;

  logic         [      7:0] r_len;
  logic         [      7:0] r_len_next;

  logic         [      2:0] r_size;
  logic         [      2:0] r_size_next;

  logic         [      1:0] r_burst;
  logic         [      1:0] r_burst_next;


  //-------------------------------------------------------------------------
  //
  // Write state machine
  //
  //-------------------------------------------------------------------------
  svc_skidbuf #(
      .DATA_WIDTH(AXI_ID_WIDTH + AXI_ADDR_WIDTH + 3 + 2)
  ) svc_skidbuf_aw_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(s_axi_awvalid),
      .i_data ({s_axi_awid, s_axi_awaddr, s_axi_awsize, s_axi_awburst}),
      .o_ready(s_axi_awready),
      .i_ready(sb_s_awready),
      .o_data ({sb_s_awid, sb_s_awaddr, sb_s_awsize, sb_s_awburst}),
      .o_valid(sb_s_awvalid)
  );

  svc_skidbuf #(
      .DATA_WIDTH(DW + AXI_STRB_WIDTH + 1)
  ) svc_skidbuf_w_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(s_axi_wvalid),
      .i_data ({s_axi_wdata, s_axi_wstrb, s_axi_wlast}),
      .o_ready(s_axi_wready),
      .i_ready(sb_s_wready),
      .o_data ({sb_s_wdata, sb_s_wstrb, sb_s_wlast}),
      .o_valid(sb_s_wvalid)
  );

  always @(*) begin
    write_state_next  = write_state;

    w_id_next         = w_id;
    w_addr_next       = w_addr;
    w_size_next       = w_size;
    w_burst_next      = w_burst;

    s_axi_bid_next    = s_axi_bid;
    s_axi_bvalid_next = s_axi_bvalid && !s_axi_bready;

    mem_wr_en         = 1'b0;
    mem_wr_addr       = 0;

    sb_s_awready      = 1'b0;
    sb_s_wready       = 1'b0;


    case (write_state)
      WRITE_STATE_IDLE: begin
        sb_s_awready = 1'b1;

        if (sb_s_awvalid && sb_s_awready) begin
          sb_s_wready      = !s_axi_bvalid || s_axi_bready;

          write_state_next = WRITE_STATE_BURST;

          w_id_next        = sb_s_awid;
          w_addr_next      = sb_s_awaddr;
          w_size_next      = sb_s_awsize;
          w_burst_next     = sb_s_awburst;

          // and also do the first write, if possible, to avoid a cycle of latency
          if (sb_s_wvalid && sb_s_wready) begin
            mem_wr_en   = 1'b1;
            mem_wr_addr = sb_s_awaddr[AW-1:LSB];

            if (sb_s_awburst != 2'b00) begin
              w_addr_next = sb_s_awaddr + (1 << sb_s_awsize);
            end

            if (sb_s_wlast) begin
              if (!s_axi_bvalid || s_axi_bready) begin
                write_state_next  = WRITE_STATE_IDLE;
                s_axi_bvalid_next = 1'b1;
                s_axi_bid_next    = sb_s_awid;
              end else begin
                write_state_next = WRITE_STATE_RESP;
              end
            end
          end
        end
      end

      WRITE_STATE_BURST: begin
        sb_s_wready = !s_axi_bvalid || s_axi_bready;

        if (sb_s_wvalid && sb_s_wready) begin
          mem_wr_en   = 1'b1;
          mem_wr_addr = w_addr[AW-1:LSB];

          if (w_burst != 2'b00) begin
            w_addr_next = w_addr + (1 << w_size);
          end

          if (sb_s_wlast) begin
            if (!s_axi_bvalid || s_axi_bready) begin
              // Don't set sb_s_awready here - if an AW is pending in the
              // skid buffer, it would be consumed but not processed since
              // we're still in BURST state. Wait for IDLE to accept next AW.
              write_state_next  = WRITE_STATE_IDLE;
              s_axi_bvalid_next = 1'b1;
              s_axi_bid_next    = w_id;
            end else begin
              write_state_next = WRITE_STATE_RESP;
            end
          end
        end
      end

      WRITE_STATE_RESP: begin
        if (s_axi_bvalid && s_axi_bready) begin
          write_state_next  = WRITE_STATE_IDLE;
          s_axi_bvalid_next = 1'b1;
          s_axi_bid_next    = w_id;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      write_state  <= WRITE_STATE_IDLE;
      s_axi_bvalid <= 1'b0;
    end else begin
      write_state  <= write_state_next;
      s_axi_bvalid <= s_axi_bvalid_next;
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
      if (mem_wr_en & sb_s_wstrb[i]) begin
        mem[mem_wr_addr][WORD_SIZE*i+:WORD_SIZE] <=
            sb_s_wdata[WORD_SIZE*i+:WORD_SIZE];
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
            mem_rd_addr       = s_axi_araddr[AW-1:LSB];

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
          mem_rd_addr       = r_addr[AW-1:LSB];

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
    s_axi_rlast <= s_axi_rlast_next;
  end

  always_ff @(posedge clk) begin
    if (mem_rd_en) begin
      s_axi_rdata <= mem[mem_rd_addr];
    end
  end

  assign s_axi_rresp = 2'b00;

`ifdef FORMAL
  `SVC_UNUSED({INIT_FILE, s_axi_awlen});
`else
  `SVC_UNUSED(s_axi_awlen);
`endif

`ifdef FORMAL
  //
  // Burst writes must consume skid buffer outputs.
  //
  // This catches cases where WRITE_STATE_BURST incorrectly
  // uses raw s_axi_w* inputs under backpressure.
  //
  always_comb begin
    if (rst_n) begin
      if (write_state == WRITE_STATE_BURST && sb_s_wvalid && sb_s_wready) begin
        assert (mem_wr_en);
      end
    end
  end

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
