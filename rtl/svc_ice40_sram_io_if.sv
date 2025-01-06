`ifndef SVC_ICE40_SRAM_IO_IF_SV
`define SVC_ICE40_SRAM_IO_IF_SV

`include "svc.sv"
`include "svc_ice40_sram_io.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

module svc_ice40_sram_io_if #(
    parameter SRAM_ADDR_WIDTH = 4,
    parameter SRAM_DATA_WIDTH = 16,
    parameter SRAM_STRB_WIDTH = (SRAM_DATA_WIDTH / 8),
    parameter SRAM_META_WIDTH = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI to SRAM interface
    //
    input  logic                       sram_cmd_valid,
    output logic                       sram_cmd_ready,
    input  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    input  logic [SRAM_META_WIDTH-1:0] sram_cmd_meta,
    input  logic                       sram_cmd_last,
    input  logic                       sram_cmd_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    input  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,

    output logic                       sram_resp_rd_valid,
    input  logic                       sram_resp_rd_ready,
    output logic [SRAM_META_WIDTH-1:0] sram_resp_rd_meta,
    output logic                       sram_resp_rd_last,
    output logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data,

    //
    // io to/from the async sram chip
    //
    output logic [SRAM_ADDR_WIDTH-1:0] sram_io_addr,
`ifndef FORMAL
    inout  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`else
    input  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`endif
    output logic                       sram_io_we_n,
    output logic                       sram_io_oe_n,
    output logic                       sram_io_ce_n
);
  localparam FIFO_WIDTH = SRAM_META_WIDTH + 1;

  typedef enum {
    STATE_IDLE,
    STATE_READ,
    STATE_WRITE
  } state_t;

  state_t                       state;
  state_t                       state_next;

  logic   [SRAM_ADDR_WIDTH-1:0] pad_addr;
  logic                         pad_wr_en;
  logic   [SRAM_DATA_WIDTH-1:0] pad_wr_data;
  logic                         pad_wr_done;
  logic   [SRAM_DATA_WIDTH-1:0] pad_rd_data;
  logic                         pad_rd_done;
  logic                         pad_ce_n;
  logic                         pad_we_n;
  logic                         pad_oe_n;


  logic                         fifo_w_inc;
  logic   [     FIFO_WIDTH-1:0] fifo_w_data;
  logic                         fifo_w_full;

  logic                         fifo_r_inc;
  logic                         fifo_r_empty;
  logic   [     FIFO_WIDTH-1:0] fifo_r_data;

  svc_ice40_sram_io #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH)
  ) svc_ice40_sram_io_i (
      .clk  (clk),
      .rst_n(rst_n),

      .pad_addr   (pad_addr),
      .pad_wr_en  (pad_wr_en),
      .pad_wr_data(pad_wr_data),
      .pad_wr_done(pad_wr_done),
      .pad_rd_data(pad_rd_data),
      .pad_rd_done(pad_rd_done),
      .pad_ce_n   (pad_ce_n),
      .pad_we_n   (pad_we_n),
      .pad_oe_n   (pad_oe_n),

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

  svc_sync_fifo #(
      .ADDR_WIDTH(2),
      .DATA_WIDTH(FIFO_WIDTH)
  ) svc_sync_fifo_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .w_inc  (fifo_w_inc),
      .w_data (fifo_w_data),
      .w_full (fifo_w_full),
      .r_inc  (fifo_r_inc),
      .r_empty(fifo_r_empty),
      .r_data (fifo_r_data)
  );

  //
  // state machine
  //
  always_comb begin
    state_next = state;

    case (state)
      STATE_IDLE: begin
        if (sram_cmd_valid && sram_cmd_ready) begin
          if (sram_cmd_wr_en) begin
            state_next = STATE_WRITE;
          end else begin
            state_next = STATE_READ;
          end
        end
      end

      STATE_READ: begin
        state_next = STATE_IDLE;
      end

      STATE_WRITE: begin
        state_next = STATE_IDLE;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Addr/data to pad
  //
  always_ff @(posedge clk) begin
    if (state_next != STATE_IDLE) begin
      pad_addr <= sram_cmd_addr;
    end

    if (state_next == STATE_WRITE) begin
      pad_wr_data <= sram_cmd_wr_data;
    end
  end

  //
  // Control signals
  //
  assign pad_ce_n = 1'b0;
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      pad_oe_n  <= 1'b1;
      pad_we_n  <= 1'b1;
      pad_wr_en <= 1'b0;
    end else begin
      pad_oe_n  <= state_next != STATE_READ;
      pad_we_n  <= state_next != STATE_WRITE;
      pad_wr_en <= state_next == STATE_WRITE || state == STATE_WRITE;
    end
  end

  assign sram_cmd_ready = state == STATE_IDLE && !fifo_w_full;

  assign fifo_w_inc     = state_next != STATE_IDLE;
  assign fifo_w_data    = {sram_cmd_meta, sram_cmd_last};
  assign fifo_r_inc     = sram_resp_rd_valid && sram_resp_rd_ready;

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      sram_resp_rd_valid <= 1'b0;
    end else begin
      if (!sram_resp_rd_valid || sram_resp_rd_ready) begin
        {sram_resp_rd_meta, sram_resp_rd_last} <= fifo_r_data;
        sram_resp_rd_data                      <= pad_rd_data;
        sram_resp_rd_valid                     <= pad_wr_done || pad_rd_done;
      end
    end
  end

  `SVC_UNUSED({sram_cmd_wr_strb, fifo_r_empty});

`ifdef FORMAL
  // TODO: this was a first pass. Think through other checks and cover
  // statements, including cover statements for latency and bubble
  // expectations.

`ifdef FORMAL_SVC_ICE40_SRAM_IO_IF
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
`ifdef FORMAL_SUBMODULE_ASSERTS
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
`else
  `define ASSERT(lable, a)
  `define ASSUME(lable, a)
`endif
  `define COVER(lable, a)
`endif
  initial assume (!rst_n);

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  //
  // assumptions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // assume incoming cmd signals are stable until accepted
      if ($past(sram_cmd_valid && !sram_cmd_ready)) begin
        `ASSUME(am_valid, sram_cmd_valid);
        `ASSUME(am_stable_addr, $stable(sram_cmd_addr));
        `ASSUME(am_stable_meta, $stable(sram_cmd_meta));
        `ASSUME(am_stable_last, $stable(sram_cmd_last));
        `ASSUME(am_stable_wr_en, $stable(sram_cmd_wr_en));
        `ASSUME(am_stable_wr_data, $stable(sram_cmd_wr_data));
      end
    end
  end

  //
  // simple assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // response signals should be stable until accepted
      if ($past(sram_resp_rd_valid && !sram_resp_rd_ready)) begin
        `ASSERT(as_stable_meta, $stable(sram_resp_rd_meta));
        `ASSERT(as_stable_last, $stable(sram_resp_rd_last));
        `ASSERT(as_stable_data, $stable(sram_resp_rd_data));
      end

      // whenever an io completes, we should always have a matching fifo
      // entry for meta data
      if ($rose(pad_wr_done) || $rose(pad_rd_done)) begin
        `ASSERT(as_fifo_rd_resp_data, !fifo_r_empty);
      end

      // we shouldn't over flow the fifo
      `ASSERT(as_overflow, !(fifo_w_full && fifo_w_inc));
    end
  end

  //
  // outstanding io tracking
  //
  // TODO: add read outstanding check
  int f_num_writes_outstanding;
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_num_writes_outstanding <= 0;
    end else begin
      if (sram_cmd_valid && sram_cmd_ready && sram_cmd_wr_en) begin
        f_num_writes_outstanding <= f_num_writes_outstanding + 1;
      end
    end
  end

  always_ff @(posedge clk) begin
    if ($past(rst_n) && rst_n) begin
      `ASSERT(as_unexpected_we, pad_we_n || f_num_writes_outstanding > 0);
    end
  end

  //
  // memory model for tracking written data
  //
  logic [SRAM_DATA_WIDTH-1:0] f_written_data[0:(1 << SRAM_ADDR_WIDTH) - 1];
  logic [(1 << SRAM_ADDR_WIDTH) - 1:0] f_written_valid;

  //
  // address of the current read response
  //
  logic [SRAM_ADDR_WIDTH-1:0] f_resp_addr;
  logic f_resp_read;

  //
  // write tracking: Update memory model on a valid write
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      // verilator lint_off: WIDTHCONCAT
      f_written_valid <= '0;
      // verilator lint_on: WIDTHCONCAT
    end else if (sram_cmd_valid && sram_cmd_wr_en && sram_cmd_ready) begin
      f_written_data[sram_cmd_addr]  <= sram_cmd_wr_data;
      f_written_valid[sram_cmd_addr] <= 1'b1;
    end
  end

  //
  // track the address for the current response
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_resp_addr <= '0;
    end else if (sram_cmd_valid && sram_cmd_ready) begin
      if (!sram_cmd_wr_en) begin
        f_resp_read <= 1'b1;
        f_resp_addr <= sram_cmd_addr;
      end else begin
        f_resp_read <= 1'b0;
      end
    end
  end

  //
  // ensure read data matches the most recent write for the address
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (sram_resp_rd_valid && sram_resp_rd_ready) begin
        if (f_written_valid[f_resp_addr]) begin
          if (f_resp_read) begin
            assert (sram_resp_rd_data == f_written_data[f_resp_addr]);
          end
        end
      end
    end
  end

  //
  // cover statements
  //
  // verilog_format: off
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `COVER(c_rd_resp, sram_resp_rd_valid && sram_resp_rd_ready);
      `COVER(c_wr, sram_cmd_valid && sram_cmd_wr_en);
      `COVER(c_rd, sram_cmd_valid && !sram_cmd_wr_en);
      `COVER(c_rd_nz, sram_resp_rd_valid && |sram_resp_rd_data);
      `COVER(c_full, fifo_w_full && $stable(fifo_w_full) && sram_cmd_valid);
      `COVER(c_full_held,
             !fifo_r_inc && fifo_w_full &&
             $stable(fifo_w_full) && sram_cmd_valid);
      `COVER(c_full_recover,
             fifo_r_inc && fifo_w_full &&
             $stable(fifo_w_full) && sram_cmd_valid);
    end
  end
  // verilog_format: on

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
