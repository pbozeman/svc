`ifndef SVC_ICE40_SRAM_IO_SV
`define SVC_ICE40_SRAM_IO_SV

`include "svc.sv"

//
// See [Lattice ICE technology Library](https://www.latticesemi.com/~/media/latticesemi/documents/technicalbriefs/sbticetechnologylibrary201701.pdf)
//
// Heavily inspired by: https://github.com/mystorm-org/BlackIce-II/blob/master/examples/sram/src/sram_sram_io_ice40.v
//
// This has a heavy use of linter pragmas because the linter is unable
// to understand what is happening inside SB_IO.
//
// Similarly, FORMAL is disabled for the SB_IO modules. sby almost
// understands them, but it complains about multiple clocks and takes
// a very long time to run before exiting with the clock errors.

// TODO: remove wr_done and change rd_done to rd_data_valid after the higher
// level axi modules are removed.
module svc_ice40_sram_io #(
    parameter integer SRAM_ADDR_WIDTH = 4,
    parameter integer SRAM_DATA_WIDTH = 16
) (
    input logic clk,
    input logic rst_n,

    // to/from the ice40 pad
    // verilator lint_off: UNUSEDSIGNAL
    input  logic [SRAM_ADDR_WIDTH-1:0] pad_addr,
    input  logic                       pad_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] pad_wr_data,
    output logic                       pad_wr_done,
    output logic                       pad_rd_done,
    // verilator lint_off: UNDRIVEN
    output logic [SRAM_DATA_WIDTH-1:0] pad_rd_data,
    // verilator lint_on: UNDRIVEN
    input  logic                       pad_ce_n,
    input  logic                       pad_we_n,
    input  logic                       pad_oe_n,

    // to/from the sram chip
    //
    // verilator lint_off: UNDRIVEN
    // These are actually driven, but the linter can't detect it happening
    // inside the SB_IO modules.
    output logic [SRAM_ADDR_WIDTH-1:0] sram_io_addr,
`ifndef FORMAL
    inout  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`else
    input  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`endif
    output logic                       sram_io_we_n,
    output logic                       sram_io_oe_n,
    output logic                       sram_io_ce_n
    // verilator lint_on: UNDRIVEN
    // verilator lint_on: UNUSEDSIGNAL
);
`ifndef FORMAL
  // This module makes use of low level lattice IP. iverilog can simulate it
  // using the yosys supplied cells_sim.v, but the dual DDR like clocking
  // doesn't interact well with sby. Rather than trying to do formal
  // assumptions on SB_IO, provide a formal version.

  //
  // cs_n (posedge)
  //
  // PIN_TYPE[5:2] = Output registered, (no enable)
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
  SB_IO #(
      .PIN_TYPE   (6'b0101_01),
      .PULLUP     (1'b0),
      .NEG_TRIGGER(1'b0)
  ) sb_sram_io_ce_n_i (
      .PACKAGE_PIN (sram_io_ce_n),
      .CLOCK_ENABLE(1'b1),
      .OUTPUT_CLK  (clk),
      .D_OUT_0     (pad_ce_n)
  );

  //
  // we_n (negedge)
  //
  // PIN_TYPE[5:2] = Output 'DDR' data is clocked out on
  //                 rising and falling clock edges.
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
  logic       pad_we_n_p1;
  logic       pad_we_n_p2;
  // verilator lint_off: UNUSEDSIGNAL
  logic [1:0] pad_we_n_ddr;
  // verilator lint_on: UNUSEDSIGNAL

  always_ff @(posedge clk) begin
    pad_we_n_p1 <= pad_we_n;
  end

  always @(negedge clk) begin
    pad_we_n_p2 <= pad_we_n_p1;
  end

  assign pad_we_n_ddr = {pad_we_n_p2, pad_we_n_p1};

  SB_IO #(
      .PIN_TYPE   (6'b0100_01),
      .PULLUP     (1'b0),
      .NEG_TRIGGER(1'b0)
  ) sb_sram_io_we_n_i (
      .PACKAGE_PIN (sram_io_we_n),
      .CLOCK_ENABLE(1'b1),
      .OUTPUT_CLK  (clk),
      .D_OUT_0     (pad_we_n_ddr[1]),
      .D_OUT_1     (pad_we_n_ddr[0])
  );

  //
  // oe_n (negedge)
  //
  // PIN_TYPE[5:2] = Output 'DDR' data is clocked out on
  //                 rising and falling clock edges.
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
  // verilator lint_off: UNUSEDSIGNAL
  logic       pad_oe_n_p1;
  logic       pad_oe_n_p2;
  logic [1:0] pad_oe_n_ddr;
  // verilator lint_on: UNUSEDSIGNAL

  always_ff @(posedge clk) begin
    pad_oe_n_p1 <= pad_oe_n;
  end

  always @(negedge clk) begin
    pad_oe_n_p2 <= pad_oe_n_p1;
  end

  assign pad_oe_n_ddr = {pad_oe_n_p2, pad_oe_n_p1};

  SB_IO #(
      .PIN_TYPE   (6'b0100_01),
      .PULLUP     (1'b0),
      .NEG_TRIGGER(1'b0)
  ) sb_sram_io_oe_n_i (
      .PACKAGE_PIN (sram_io_oe_n),
      .CLOCK_ENABLE(1'b1),
      .OUTPUT_CLK  (clk),
      .D_OUT_0     (pad_oe_n_ddr[1]),
      .D_OUT_1     (pad_oe_n_ddr[0])
  );

  //
  // addr (posedge)
  //
  // PIN_TYPE[5:2] = Output registered, (no enable)
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
  SB_IO #(
      .PIN_TYPE   (6'b0101_01),
      .PULLUP     (1'b0),
      .NEG_TRIGGER(1'b0)
  ) sb_sram_io_addr_i[SRAM_ADDR_WIDTH-1:0] (
      .PACKAGE_PIN (sram_io_addr),
      .CLOCK_ENABLE(1'b1),
      .OUTPUT_CLK  (clk),
      .D_OUT_0     (pad_addr)
  );

  //
  // data (posedge output, negedge input)
  //
  // PIN_TYPE[5:2] = Output registered and enable registered
  // PIN_TYPE[1:0] = Input 'DDR' data is clocked out on rising
  //                 and falling clock edges. Use the D_IN_0
  //                 and D_IN_1 pins for DDR operation.
  //
  logic [SRAM_DATA_WIDTH-1:0] pad_rd_data_p1;

  SB_IO #(
      .PIN_TYPE   (6'b1101_00),
      .PULLUP     (1'b0),
      .NEG_TRIGGER(1'b0)
  ) sb_sram_io_sram_io_data_i[SRAM_DATA_WIDTH-1:0] (
      .PACKAGE_PIN      (sram_io_data),
      .LATCH_INPUT_VALUE(1'b1),
      .CLOCK_ENABLE     (1'b1),
      .INPUT_CLK        (clk),
      .OUTPUT_CLK       (clk),
      .OUTPUT_ENABLE    (pad_wr_en),
      .D_OUT_0          (pad_wr_data),
      .D_OUT_1          (pad_wr_data),
      .D_IN_1           (pad_rd_data_p1)
  );

  // oe non-neg version
  logic pad_oe_p2 = 1'b0;

  always_ff @(posedge clk) begin
    if (pad_oe_p2) begin
      pad_rd_data <= pad_rd_data_p1;
      pad_rd_done <= 1'b1;
    end else begin
      pad_rd_done <= 1'b0;
    end

    pad_oe_p2 <= !pad_oe_n_p1;
  end

  // we non-neg version
  logic pad_we_p2 = 1'b0;

  always_ff @(posedge clk) begin
    if (pad_we_p2) begin
      pad_wr_done <= 1'b1;
    end else begin
      pad_wr_done <= 1'b0;
    end

    pad_we_p2 <= !pad_we_n_p1;
  end

`else  // FORMAL
  // This is strictly a fake/model for use with formal testing of a calling
  // module. Given the SB_IO cell simulation of lattice IP with DDR clocks,
  // tri-state IO, etc, it's likely that synthesizeable part of this module
  // is not easily formally tested, or at least, not worth the effort to
  // figure out.
  localparam DW = SRAM_DATA_WIDTH;
  localparam AW = SRAM_ADDR_WIDTH;

  // Memory array to store data
  logic [DW-1:0] mem       [0:(1 << AW)-1];

  // Internal signals to match non-formal implementation timing
  logic          pad_oe_p2;
  logic          pad_we_p2;

  always @(negedge pad_we_n) begin
    // verilator lint_off: BLKSEQ
    mem[pad_addr] = pad_wr_data;
    // verilator lint_on: BLKSEQ
  end

  always @(negedge pad_oe_n) begin
    // verilator lint_off: BLKSEQ
    pad_rd_data = mem[pad_addr];
    // verilator lint_on: BLKSEQ
  end

  // Register the negative enables to match main implementation
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pad_oe_p2   <= 1'b0;
      pad_we_p2   <= 1'b0;
      pad_rd_done <= 1'b0;
      pad_wr_done <= 1'b0;
    end else begin
      // Match timing of main implementation
      pad_oe_p2 <= !pad_oe_n;
      pad_we_p2 <= !pad_we_n;

      // Read completion logic
      if (pad_oe_p2) begin
        pad_rd_done <= 1'b1;
      end else begin
        pad_rd_done <= 1'b0;
      end

      // Write completion logic
      if (pad_we_p2) begin
        pad_wr_done <= 1'b1;
      end else begin
        pad_wr_done <= 1'b0;
      end
    end
  end

  // Drive SRAM signals
  assign sram_io_addr = pad_addr;
  assign sram_io_we_n = pad_we_n;
  assign sram_io_oe_n = pad_oe_n;
  assign sram_io_ce_n = pad_ce_n;

  // Assertions
  always @(posedge clk) begin
    if (rst_n) begin
      // Cannot read and write simultaneously
      a_rd_or_wr : assert (pad_oe_n || pad_we_n);
    end
  end

`endif
endmodule
`endif
