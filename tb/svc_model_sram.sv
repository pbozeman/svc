`ifndef SVC_MODEL_SRAM_SV
`define SVC_MODEL_SRAM_SV

`include "svc.sv"

// This is a fake/model of an async sram chip. It is intended for use in test
// test benches. It will raise errors if the caller violates setup and hold
// times for the chip, or if they try to drive the bus while also reading, it,
// etc.
//
// This file is full of un-synthesizable constructs and what would normally be
// bad practices, but this is all to get the timings exactly correct to ensure
// that the callers are meeting the nanosecond level setup and hold times of
// real async sram chips.

module svc_model_sram #(
    parameter ADDR_WIDTH                = 10,
    parameter DATA_WIDTH                = 8,
    parameter UNINITIALIZED_READS_FATAL = 1,
    parameter INJECT_ERROR              = 0,

    // timings (in ns)
    parameter real tAA  = 10,   // Address Access Time
    parameter real tOHA = 2.5,  // Output Hold Time
    parameter real tDOE = 6,    // OE# Access Time
    parameter real tAW  = 8,    // Address Setup Time to Write End

    parameter BAD_DATA = 1'bx
) (
    input logic rst_n,

    input logic                  we_n,
    input logic                  oe_n,
    input logic                  ce_n,
    input logic [ADDR_WIDTH-1:0] addr,
    inout logic [DATA_WIDTH-1:0] data_io
);

  // memory
  logic [DATA_WIDTH-1:0] sram_mem         [0:(1 << ADDR_WIDTH)-1];

  // data written to bus, possibly tri-state if output not enabled
  logic                  output_active;
  logic [DATA_WIDTH-1:0] data_out;


  // Previous data for output hold time
  logic [DATA_WIDTH-1:0] prev_data;

  // Time of last address change
  real                   last_addr_change;

  // Time of last OE# falling edge
  real                   last_oe_fall;

  // Data signals
  assign output_active = !ce_n && !oe_n;
  assign data_io       = output_active ? data_out : {DATA_WIDTH{1'bz}};

  // Delayed address update and data handling
  always @(addr) begin
    // verilator lint_off BLKSEQ
    prev_data        = data_out;
    last_addr_change = $realtime;
    // verilator lint_on BLKSEQ
  end

  // Track OE# falling edge
  always @(negedge oe_n) begin
    // verilator lint_off BLKSEQ
    data_out     = {DATA_WIDTH{1'bz}};
    last_oe_fall = $realtime;
    // verilator lint_on BLKSEQ
  end

  always begin
    if (output_active) begin
      if ($realtime - last_oe_fall < tDOE) begin
        data_out = {DATA_WIDTH{1'bz}};
      end else if ($realtime - last_addr_change < tOHA) begin
        data_out = prev_data;
      end else if ($realtime - last_addr_change < tAA) begin
        data_out = {DATA_WIDTH{BAD_DATA}};
      end else begin
        if (sram_mem[addr] === {DATA_WIDTH{1'bx}}) begin
          if (UNINITIALIZED_READS_FATAL) begin
            $display("read from unitialized addr %h", addr);
            $fatal;
          end else begin
            data_out = DATA_WIDTH'(addr);
          end
        end else begin
          data_out = sram_mem[addr];
        end
      end
    end

    #0.01;
  end

  // Write operation
  logic write_enable = 0;

  always @(*) begin
    // verilator lint_off SYNCASYNCNET
    // verilator lint_off BLKSEQ
    if (!we_n && !ce_n) begin
      #(tAW) write_enable = 1;
    end else begin
      write_enable = 0;
    end
    // verilator lint_on BLKSEQ
    // verilator lint_on SYNCASYNCNET
  end

  // We do immediate assignment so that our timings are explicit.
  // (Note: tAW to write_enabled is delayed.)
  always_latch begin
    if (write_enable) begin
      if (INJECT_ERROR && addr == {ADDR_WIDTH{1'b1}}) begin
        sram_mem[addr] = {DATA_WIDTH{1'b1}};
      end else if (!we_n) begin
        sram_mem[addr] = data_io;
      end
    end
  end

  logic [ADDR_WIDTH-1:0] oe_n_initial_addr;
  logic [ADDR_WIDTH-1:0] we_n_initial_addr;
  logic [DATA_WIDTH-1:0] we_n_initial_data;

  always @(negedge oe_n) begin
    if (!ce_n) begin
      // Do not add rst_n to this check, we don't ever want this to happen as it
      // can damage the hardwaare
      if (data_io !== {DATA_WIDTH{1'bz}}) begin
        $display("oe_n low while fpga driving bus");
        $fatal;
      end
      oe_n_initial_addr <= addr;
    end
  end

  always begin
    if (!oe_n) begin
      if (oe_n_initial_addr != addr && rst_n) begin
        $display("addr changed during read, old: %h new: %h",
                 oe_n_initial_addr, addr);
        $fatal;
      end
    end
    #0.01;
  end

  always @(negedge we_n) begin
    if (!ce_n) begin
      we_n_initial_addr <= addr;
    end
  end

  always begin
    if (!we_n) begin
      if (we_n_initial_data === 'x || we_n_initial_data === 'z) begin
        // verilator lint_off BLKSEQ
        we_n_initial_data = data_io;
        // verilator lint_on BLKSEQ
      end else begin
        if (we_n_initial_data !== data_io && rst_n) begin
          $display("data changed during write %h %h", we_n_initial_data,
                   data_io);
          $fatal;
        end
      end
    end

    #0.01;
  end

  always @(posedge we_n) begin
    if (we_n_initial_addr !== addr && rst_n) begin
      $display("addr changed during write");
      $fatal;
    end

    // ensure data hold. Note: the sram chip does not require a hold time,
    // but we want to make sure the fpga is actually still driving the
    // signal at the time we_n goes high.
    #1 begin
      if (data_io === 'z && rst_n) begin
        $display("data not held past we_n");
        $fatal;
      end
    end

    we_n_initial_data <= 'x;
  end
endmodule
`endif
