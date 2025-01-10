`ifndef SVC_ICE40_SRAM_IO_IF_SV
`define SVC_ICE40_SRAM_IO_IF_SV

`include "svc.sv"
`include "svc_ice40_sram_io.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

module svc_ice40_sram_io_if #(
    parameter SRAM_ADDR_WIDTH = 4,
    parameter SRAM_DATA_WIDTH = 16,
    parameter SRAM_STRB_WIDTH = (SRAM_DATA_WIDTH / 8)
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI to SRAM interface
    //
    input  logic                       sram_cmd_valid,
    output logic                       sram_cmd_ready,
    input  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    input  logic                       sram_cmd_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    input  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,

    output logic                       sram_resp_rd_valid,
    input  logic                       sram_resp_rd_ready,
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
  localparam FIFO_ADDR_WIDTH = 1;
  localparam FIFO_DATA_WIDTH = SRAM_DATA_WIDTH;

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
  logic   [SRAM_DATA_WIDTH-1:0] pad_rd_data;
  logic                         pad_rd_valid;
  logic                         pad_ce_n;
  logic                         pad_we_n;
  logic                         pad_oe_n;

  // response fifo signals
  logic                         fifo_w_half_full;
  logic                         fifo_r_empty;

  svc_ice40_sram_io #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH)
  ) svc_ice40_sram_io_i (
      .clk  (clk),
      .rst_n(rst_n),

      .pad_addr    (pad_addr),
      .pad_wr_en   (pad_wr_en),
      .pad_wr_data (pad_wr_data),
      .pad_rd_data (pad_rd_data),
      .pad_rd_valid(pad_rd_valid),
      .pad_ce_n    (pad_ce_n),
      .pad_we_n    (pad_we_n),
      .pad_oe_n    (pad_oe_n),

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
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

  assign sram_cmd_ready = (state == STATE_IDLE && !fifo_w_half_full);

  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(FIFO_DATA_WIDTH)
  ) svc_sync_fifo_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (pad_rd_valid),
      .w_data     (pad_rd_data),
      .w_full     (),
      .w_half_full(fifo_w_half_full),
      .r_inc      (sram_resp_rd_valid && sram_resp_rd_ready),
      .r_data     (sram_resp_rd_data),
      .r_empty    (fifo_r_empty)
  );

  assign sram_resp_rd_valid = !fifo_r_empty;

  `SVC_UNUSED({sram_cmd_wr_strb});

`ifdef FORMAL
`ifdef FORMAL_SVC_ICE40_SRAM_IO_IF
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
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
    `ASSUME(am_strb, sram_cmd_wr_strb == 0);
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // assume incoming cmd signals are stable until accepted
      if ($past(sram_cmd_valid && !sram_cmd_ready)) begin
        `ASSUME(am_valid, sram_cmd_valid);
        `ASSUME(am_stable_addr, $stable(sram_cmd_addr));
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
        `ASSERT(as_stable_data, $stable(sram_resp_rd_data));
      end
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
  // address read tracking
  //
  logic f_fifo_w_full;
  logic f_fifo_r_empty;
  logic f_mem_past_valid;
  logic [SRAM_DATA_WIDTH-1:0] f_mem_past_data;

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

  // We have to capture the values of mem valid/data now, because the solver
  // will otherwise try to break us by doing a write while having stalled
  // the read response.
  svc_sync_fifo #(
      .ADDR_WIDTH(3),
      .DATA_WIDTH(1 + SRAM_DATA_WIDTH)
  ) f_fifo_i (
      .clk(clk),
      .rst_n(rst_n),
      .w_inc(sram_cmd_valid && sram_cmd_ready && !sram_cmd_wr_en),
      .w_data({f_written_valid[sram_cmd_addr], f_written_data[sram_cmd_addr]}),
      .w_full(f_fifo_w_full),
      .w_half_full(),
      .r_inc(sram_resp_rd_valid && sram_resp_rd_ready),
      .r_data({f_mem_past_valid, f_mem_past_data}),
      .r_empty(f_fifo_r_empty)
  );

  //
  // ensure read data matches the most recent write for the address
  //
  always_ff @(posedge clk) begin
    // the fifo was sized such that it shouldn't overflow
    `ASSERT(as_fifo_full, !f_fifo_w_full);
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (sram_resp_rd_valid && sram_resp_rd_ready) begin
        assert (!f_fifo_r_empty);
        if (f_mem_past_valid) begin
          `ASSERT(as_data_match, sram_resp_rd_data == f_mem_past_data);
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
      `COVER(c_resp_rd, sram_resp_rd_valid && sram_resp_rd_ready);
      `COVER(c_resp_rd_nz, sram_resp_rd_valid && |sram_resp_rd_data);
      `COVER(c_cmd_wr, sram_cmd_valid && sram_cmd_wr_en);
      `COVER(c_cmd_rd, sram_cmd_valid && !sram_cmd_wr_en);
      `COVER(c_cmd_stall, sram_cmd_valid && !sram_cmd_ready);
      `COVER(c_resp_stall, sram_resp_rd_valid && !sram_resp_rd_ready);
    end
  end
  // verilog_format: on

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
