`ifndef SVC_AXI_MEM_LATENCY_SV
`define SVC_AXI_MEM_LATENCY_SV

`include "svc.sv"
`include "svc_axi_mem.sv"

//
// AXI memory wrapper with configurable latency injection.
//
// Wraps svc_axi_mem and adds delays to simulate DDR3/MIG-like timing.
// Used for reproducing timing-sensitive bugs in simulation.
//
// Latency parameters:
// - AW_ACCEPT_LATENCY: Cycles before awready after awvalid
// - W_ACCEPT_LATENCY: Cycles before wready after wvalid
// - READ_RESP_LATENCY: Cycles between AR handshake and first R beat
// - WRITE_RESP_LATENCY: Cycles between last W beat and B response
//
// Random latency mode (RANDOM_LATENCY=1):
// - Each transaction gets a random delay between MIN and MAX values
// - *_MIN parameters default to 1 if not specified
// - *_LATENCY parameters become the maximum when RANDOM_LATENCY=1
//
// When latency is 0, behavior is pass-through (minimal overhead).
//
module svc_axi_mem_latency #(
    parameter int AXI_ADDR_WIDTH = 8,
    parameter int AXI_DATA_WIDTH = 16,
    parameter int AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter int AXI_ID_WIDTH   = 4,

    // Latency injection (cycles) - also used as MAX when RANDOM_LATENCY=1
    parameter int AW_ACCEPT_LATENCY  = 0,
    parameter int W_ACCEPT_LATENCY   = 0,
    parameter int READ_RESP_LATENCY  = 0,
    parameter int WRITE_RESP_LATENCY = 0,

    // Minimum latencies for random mode (defaults to 1)
    parameter int AW_ACCEPT_LATENCY_MIN  = 1,
    parameter int W_ACCEPT_LATENCY_MIN   = 1,
    parameter int READ_RESP_LATENCY_MIN  = 1,
    parameter int WRITE_RESP_LATENCY_MIN = 1,

    // Enable randomized latency (uses $urandom_range)
    parameter bit RANDOM_LATENCY = 0,

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

  // State encodings (use localparam for Icarus compatibility)
  localparam logic [1:0] RD_IDLE = 2'd0;
  localparam logic [1:0] RD_DELAY = 2'd1;
  localparam logic [1:0] RD_FORWARD = 2'd2;
  localparam logic [1:0] RD_BURST = 2'd3;

  localparam logic [1:0] WR_IDLE = 2'd0;
  localparam logic [1:0] WR_DELAY = 2'd1;
  localparam logic [1:0] WR_RESPOND = 2'd2;

  localparam logic [1:0] AW_IDLE = 2'd0;
  localparam logic [1:0] AW_DELAY = 2'd1;
  localparam logic [1:0] AW_FORWARD = 2'd2;

  localparam logic [1:0] W_IDLE = 2'd0;
  localparam logic [1:0] W_DELAY = 2'd1;
  localparam logic [1:0] W_FORWARD = 2'd2;

  // Internal signals to/from svc_axi_mem
  logic                      mem_axi_awvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_awid;
  logic [AXI_ADDR_WIDTH-1:0] mem_axi_awaddr;
  logic [               7:0] mem_axi_awlen;
  logic [               2:0] mem_axi_awsize;
  logic [               1:0] mem_axi_awburst;
  logic                      mem_axi_awready;

  logic                      mem_axi_wvalid;
  logic [AXI_DATA_WIDTH-1:0] mem_axi_wdata;
  logic [AXI_STRB_WIDTH-1:0] mem_axi_wstrb;
  logic                      mem_axi_wlast;
  logic                      mem_axi_wready;

  logic                      mem_axi_arvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_arid;
  logic [AXI_ADDR_WIDTH-1:0] mem_axi_araddr;
  logic [               7:0] mem_axi_arlen;
  logic [               2:0] mem_axi_arsize;
  logic [               1:0] mem_axi_arburst;
  logic                      mem_axi_arready;

  logic                      mem_axi_rvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_rid;
  logic [AXI_DATA_WIDTH-1:0] mem_axi_rdata;
  logic [               1:0] mem_axi_rresp;
  logic                      mem_axi_rlast;
  logic                      mem_axi_rready;

  logic                      mem_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_bid;
  logic [               1:0] mem_axi_bresp;
  logic                      mem_axi_bready;

  //
  // Underlying memory
  //
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_STRB_WIDTH(AXI_STRB_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .INIT_FILE     (INIT_FILE)
  ) axi_mem_inst (
      .clk  (clk),
      .rst_n(rst_n),

      // Write address - through delay logic
      .s_axi_awvalid(mem_axi_awvalid),
      .s_axi_awid   (mem_axi_awid),
      .s_axi_awaddr (mem_axi_awaddr),
      .s_axi_awlen  (mem_axi_awlen),
      .s_axi_awsize (mem_axi_awsize),
      .s_axi_awburst(mem_axi_awburst),
      .s_axi_awready(mem_axi_awready),

      // Write data - through delay logic
      .s_axi_wvalid(mem_axi_wvalid),
      .s_axi_wdata (mem_axi_wdata),
      .s_axi_wstrb (mem_axi_wstrb),
      .s_axi_wlast (mem_axi_wlast),
      .s_axi_wready(mem_axi_wready),

      // Write response - to delay logic
      .s_axi_bvalid(mem_axi_bvalid),
      .s_axi_bid   (mem_axi_bid),
      .s_axi_bresp (mem_axi_bresp),
      .s_axi_bready(mem_axi_bready),

      // Read address - to delay logic
      .s_axi_arvalid(mem_axi_arvalid),
      .s_axi_arid   (mem_axi_arid),
      .s_axi_araddr (mem_axi_araddr),
      .s_axi_arlen  (mem_axi_arlen),
      .s_axi_arsize (mem_axi_arsize),
      .s_axi_arburst(mem_axi_arburst),
      .s_axi_arready(mem_axi_arready),

      // Read data - from delay logic
      .s_axi_rvalid(mem_axi_rvalid),
      .s_axi_rid   (mem_axi_rid),
      .s_axi_rdata (mem_axi_rdata),
      .s_axi_rresp (mem_axi_rresp),
      .s_axi_rlast (mem_axi_rlast),
      .s_axi_rready(mem_axi_rready)
  );

  //=========================================================================
  // AW (Write Address) latency injection
  //=========================================================================
  generate
    if (AW_ACCEPT_LATENCY == 0) begin : g_no_aw_latency
      // Pass through
      assign mem_axi_awvalid = s_axi_awvalid;
      assign mem_axi_awid    = s_axi_awid;
      assign mem_axi_awaddr  = s_axi_awaddr;
      assign mem_axi_awlen   = s_axi_awlen;
      assign mem_axi_awsize  = s_axi_awsize;
      assign mem_axi_awburst = s_axi_awburst;
      assign s_axi_awready   = mem_axi_awready;

    end else begin : g_aw_latency
      // Delay AW acceptance

      logic [               1:0] aw_state;
      logic [               1:0] aw_state_next;

      // Captured request
      logic [  AXI_ID_WIDTH-1:0] aw_id;
      logic [AXI_ADDR_WIDTH-1:0] aw_addr;
      logic [               7:0] aw_len;
      logic [               2:0] aw_size;
      logic [               1:0] aw_burst;

      localparam int AW_CNT_W = $clog2(AW_ACCEPT_LATENCY + 1);
      logic [AW_CNT_W-1:0] aw_delay_cnt;

      // Random delay generation
      function automatic [AW_CNT_W-1:0] get_aw_delay();
        if (RANDOM_LATENCY) begin
          // verilog_lint: waive-start line-length
          return AW_CNT_W'($urandom_range(
              AW_ACCEPT_LATENCY - 1, AW_ACCEPT_LATENCY_MIN - 1
          ));
          // verilog_lint: waive-stop line-length
        end else begin
          return AW_CNT_W'(AW_ACCEPT_LATENCY - 1);
        end
      endfunction

      // Outputs
      assign mem_axi_awvalid = (aw_state == AW_FORWARD);
      assign mem_axi_awid    = aw_id;
      assign mem_axi_awaddr  = aw_addr;
      assign mem_axi_awlen   = aw_len;
      assign mem_axi_awsize  = aw_size;
      assign mem_axi_awburst = aw_burst;

      assign s_axi_awready   = (aw_state == AW_IDLE);

      // State transitions
      always_comb begin
        aw_state_next = aw_state;

        case (aw_state)
          AW_IDLE: begin
            if (s_axi_awvalid && s_axi_awready) begin
              aw_state_next = AW_DELAY;
            end
          end

          AW_DELAY: begin
            if (aw_delay_cnt == 0) begin
              aw_state_next = AW_FORWARD;
            end
          end

          AW_FORWARD: begin
            if (mem_axi_awready) begin
              aw_state_next = AW_IDLE;
            end
          end

          default: aw_state_next = AW_IDLE;
        endcase
      end

      always_ff @(posedge clk) begin
        if (!rst_n) begin
          aw_state     <= AW_IDLE;
          aw_delay_cnt <= '0;
          aw_id        <= '0;
          aw_addr      <= '0;
          aw_len       <= '0;
          aw_size      <= '0;
          aw_burst     <= '0;
        end else begin
          aw_state <= aw_state_next;

          case (aw_state)
            AW_IDLE: begin
              if (s_axi_awvalid && s_axi_awready) begin
                aw_id        <= s_axi_awid;
                aw_addr      <= s_axi_awaddr;
                aw_len       <= s_axi_awlen;
                aw_size      <= s_axi_awsize;
                aw_burst     <= s_axi_awburst;
                aw_delay_cnt <= get_aw_delay();
              end
            end

            AW_DELAY: begin
              if (aw_delay_cnt > 0) begin
                aw_delay_cnt <= aw_delay_cnt - 1;
              end
            end

            default: ;
          endcase
        end
      end
    end
  endgenerate

  //=========================================================================
  // W (Write Data) latency injection
  //=========================================================================
  generate
    if (W_ACCEPT_LATENCY == 0) begin : g_no_w_latency
      // Pass through
      assign mem_axi_wvalid = s_axi_wvalid;
      assign mem_axi_wdata  = s_axi_wdata;
      assign mem_axi_wstrb  = s_axi_wstrb;
      assign mem_axi_wlast  = s_axi_wlast;
      assign s_axi_wready   = mem_axi_wready;

    end else begin : g_w_latency
      // Delay W acceptance

      logic [               1:0] w_state;
      logic [               1:0] w_state_next;

      // Captured request
      logic [AXI_DATA_WIDTH-1:0] w_data;
      logic [AXI_STRB_WIDTH-1:0] w_strb;
      logic                      w_last;

      localparam int W_CNT_W = $clog2(W_ACCEPT_LATENCY + 1);
      logic [W_CNT_W-1:0] w_delay_cnt;

      // Random delay generation
      function automatic [W_CNT_W-1:0] get_w_delay();
        if (RANDOM_LATENCY) begin
          // verilog_lint: waive-start line-length
          return W_CNT_W'($urandom_range(
              W_ACCEPT_LATENCY - 1, W_ACCEPT_LATENCY_MIN - 1
          ));
          // verilog_lint: waive-stop line-length
        end else begin
          return W_CNT_W'(W_ACCEPT_LATENCY - 1);
        end
      endfunction

      // Outputs
      assign mem_axi_wvalid = (w_state == W_FORWARD);
      assign mem_axi_wdata  = w_data;
      assign mem_axi_wstrb  = w_strb;
      assign mem_axi_wlast  = w_last;

      assign s_axi_wready   = (w_state == W_IDLE);

      // State transitions
      always_comb begin
        w_state_next = w_state;

        case (w_state)
          W_IDLE: begin
            if (s_axi_wvalid && s_axi_wready) begin
              w_state_next = W_DELAY;
            end
          end

          W_DELAY: begin
            if (w_delay_cnt == 0) begin
              w_state_next = W_FORWARD;
            end
          end

          W_FORWARD: begin
            if (mem_axi_wready) begin
              w_state_next = W_IDLE;
            end
          end

          default: w_state_next = W_IDLE;
        endcase
      end

      always_ff @(posedge clk) begin
        if (!rst_n) begin
          w_state     <= W_IDLE;
          w_delay_cnt <= '0;
          w_data      <= '0;
          w_strb      <= '0;
          w_last      <= '0;
        end else begin
          w_state <= w_state_next;

          case (w_state)
            W_IDLE: begin
              if (s_axi_wvalid && s_axi_wready) begin
                w_data      <= s_axi_wdata;
                w_strb      <= s_axi_wstrb;
                w_last      <= s_axi_wlast;
                w_delay_cnt <= get_w_delay();
              end
            end

            W_DELAY: begin
              if (w_delay_cnt > 0) begin
                w_delay_cnt <= w_delay_cnt - 1;
              end
            end

            default: ;
          endcase
        end
      end
    end
  endgenerate

  //=========================================================================
  // Read latency injection
  //=========================================================================
  //
  // Strategy: Accept AR from external, delay before forwarding to mem.
  // This creates the latency between request and first response.
  //
  generate
    if (READ_RESP_LATENCY == 0) begin : g_no_read_latency
      // Pass through
      assign mem_axi_arvalid = s_axi_arvalid;
      assign mem_axi_arid    = s_axi_arid;
      assign mem_axi_araddr  = s_axi_araddr;
      assign mem_axi_arlen   = s_axi_arlen;
      assign mem_axi_arsize  = s_axi_arsize;
      assign mem_axi_arburst = s_axi_arburst;
      assign s_axi_arready   = mem_axi_arready;

      assign s_axi_rvalid    = mem_axi_rvalid;
      assign s_axi_rid       = mem_axi_rid;
      assign s_axi_rdata     = mem_axi_rdata;
      assign s_axi_rresp     = mem_axi_rresp;
      assign s_axi_rlast     = mem_axi_rlast;
      assign mem_axi_rready  = s_axi_rready;

    end else begin : g_read_latency
      // Delay read requests before forwarding to memory

      logic [               1:0] rd_state;
      logic [               1:0] rd_state_next;

      // Captured request
      logic [  AXI_ID_WIDTH-1:0] rd_id;
      logic [AXI_ADDR_WIDTH-1:0] rd_addr;
      logic [               7:0] rd_len;
      logic [               2:0] rd_size;
      logic [               1:0] rd_burst;

      // Delay counter width calculation
      localparam int RD_CNT_W = $clog2(READ_RESP_LATENCY + 1);
      logic [RD_CNT_W-1:0] rd_delay_cnt;

      // Random delay generation
      function automatic [RD_CNT_W-1:0] get_rd_delay();
        if (RANDOM_LATENCY) begin
          // verilog_lint: waive-start line-length
          return RD_CNT_W'($urandom_range(
              READ_RESP_LATENCY - 1, READ_RESP_LATENCY_MIN - 1
          ));
          // verilog_lint: waive-stop line-length
        end else begin
          return RD_CNT_W'(READ_RESP_LATENCY - 1);
        end
      endfunction

      // Outputs
      assign mem_axi_arvalid = (rd_state == RD_FORWARD);
      assign mem_axi_arid    = rd_id;
      assign mem_axi_araddr  = rd_addr;
      assign mem_axi_arlen   = rd_len;
      assign mem_axi_arsize  = rd_size;
      assign mem_axi_arburst = rd_burst;

      assign s_axi_arready   = (rd_state == RD_IDLE);

      // Pass through read data channel
      assign s_axi_rvalid    = mem_axi_rvalid;
      assign s_axi_rid       = mem_axi_rid;
      assign s_axi_rdata     = mem_axi_rdata;
      assign s_axi_rresp     = mem_axi_rresp;
      assign s_axi_rlast     = mem_axi_rlast;
      assign mem_axi_rready  = s_axi_rready;

      // State transitions
      always_comb begin
        rd_state_next = rd_state;

        case (rd_state)
          RD_IDLE: begin
            if (s_axi_arvalid && s_axi_arready) begin
              rd_state_next = RD_DELAY;
            end
          end

          RD_DELAY: begin
            if (rd_delay_cnt == 0) begin
              rd_state_next = RD_FORWARD;
            end
          end

          RD_FORWARD: begin
            if (mem_axi_arready) begin
              rd_state_next = RD_BURST;
            end
          end

          RD_BURST: begin
            // Wait for burst to complete
            if (mem_axi_rvalid && mem_axi_rready && mem_axi_rlast) begin
              rd_state_next = RD_IDLE;
            end
          end

          default: rd_state_next = RD_IDLE;
        endcase
      end

      always_ff @(posedge clk) begin
        if (!rst_n) begin
          rd_state     <= RD_IDLE;
          rd_delay_cnt <= '0;
          rd_id        <= '0;
          rd_addr      <= '0;
          rd_len       <= '0;
          rd_size      <= '0;
          rd_burst     <= '0;
        end else begin
          rd_state <= rd_state_next;

          case (rd_state)
            RD_IDLE: begin
              if (s_axi_arvalid && s_axi_arready) begin
                // Capture request and start delay
                rd_id        <= s_axi_arid;
                rd_addr      <= s_axi_araddr;
                rd_len       <= s_axi_arlen;
                rd_size      <= s_axi_arsize;
                rd_burst     <= s_axi_arburst;
                rd_delay_cnt <= get_rd_delay();
              end
            end

            RD_DELAY: begin
              if (rd_delay_cnt > 0) begin
                rd_delay_cnt <= rd_delay_cnt - 1;
              end
            end

            default: ;
          endcase
        end
      end
    end
  endgenerate

  //=========================================================================
  // Write response latency injection
  //=========================================================================
  generate
    if (WRITE_RESP_LATENCY == 0) begin : g_no_write_latency
      // Pass through
      assign s_axi_bvalid   = mem_axi_bvalid;
      assign s_axi_bid      = mem_axi_bid;
      assign s_axi_bresp    = mem_axi_bresp;
      assign mem_axi_bready = s_axi_bready;

    end else begin : g_write_latency
      // Delay write responses

      logic [             1:0] wr_state;
      logic [             1:0] wr_state_next;

      logic [AXI_ID_WIDTH-1:0] wr_id;
      logic [             1:0] wr_resp;

      localparam int WR_CNT_W = $clog2(WRITE_RESP_LATENCY + 1);
      logic [WR_CNT_W-1:0] wr_delay_cnt;

      // Random delay generation
      function automatic [WR_CNT_W-1:0] get_wr_delay();
        if (RANDOM_LATENCY) begin
          // verilog_lint: waive-start line-length
          return WR_CNT_W'($urandom_range(
              WRITE_RESP_LATENCY - 1, WRITE_RESP_LATENCY_MIN - 1
          ));
          // verilog_lint: waive-stop line-length
        end else begin
          return WR_CNT_W'(WRITE_RESP_LATENCY - 1);
        end
      endfunction

      assign s_axi_bvalid   = (wr_state == WR_RESPOND);
      assign s_axi_bid      = wr_id;
      assign s_axi_bresp    = wr_resp;
      assign mem_axi_bready = (wr_state == WR_IDLE);

      always_comb begin
        wr_state_next = wr_state;

        case (wr_state)
          WR_IDLE: begin
            if (mem_axi_bvalid && mem_axi_bready) begin
              wr_state_next = WR_DELAY;
            end
          end

          WR_DELAY: begin
            if (wr_delay_cnt == 0) begin
              wr_state_next = WR_RESPOND;
            end
          end

          WR_RESPOND: begin
            if (s_axi_bready) begin
              wr_state_next = WR_IDLE;
            end
          end

          default: wr_state_next = WR_IDLE;
        endcase
      end

      always_ff @(posedge clk) begin
        if (!rst_n) begin
          wr_state     <= WR_IDLE;
          wr_delay_cnt <= '0;
          wr_id        <= '0;
          wr_resp      <= '0;
        end else begin
          wr_state <= wr_state_next;

          case (wr_state)
            WR_IDLE: begin
              if (mem_axi_bvalid && mem_axi_bready) begin
                wr_id        <= mem_axi_bid;
                wr_resp      <= mem_axi_bresp;
                wr_delay_cnt <= get_wr_delay();
              end
            end

            WR_DELAY: begin
              if (wr_delay_cnt > 0) begin
                wr_delay_cnt <= wr_delay_cnt - 1;
              end
            end

            default: ;
          endcase
        end
      end
    end
  endgenerate

endmodule
`endif
