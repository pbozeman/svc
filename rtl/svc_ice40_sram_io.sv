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

module svc_ice40_sram_io #(
    parameter integer SRAM_ADDR_WIDTH = 4,
    parameter integer SRAM_DATA_WIDTH = 16
) (
    input logic clk,
    // verilator lint_off: UNUSEDSIGNAL
    input logic rst_n,
    // verilator lint_on: UNUSEDSIGNAL

    // to/from the ice40 pad
    // verilator lint_off: UNUSEDSIGNAL
    input  logic [SRAM_ADDR_WIDTH-1:0] pad_addr,
    input  logic                       pad_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] pad_wr_data,
    output logic                       pad_rd_valid,
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
    // verilator lint_off: MULTIDRIVEN
    input  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
    // verilator lint_on: MULTIDRIVEN
`endif
    output logic                       sram_io_we_n,
    output logic                       sram_io_oe_n,
    output logic                       sram_io_ce_n
    // verilator lint_on: UNDRIVEN
    // verilator lint_on: UNUSEDSIGNAL
);
`ifdef VERILATOR
`ifndef NO_SB_IO
  `define NO_SB_IO
`endif
`endif

`ifndef FORMAL
  //
  // cs_n (posedge)
  //
  // PIN_TYPE[5:2] = Output registered, (no enable)
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
`ifndef NO_SB_IO
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
`endif

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

`ifndef NO_SB_IO
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
`endif

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

`ifndef NO_SB_IO
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
`endif

  //
  // addr (posedge)
  //
  // PIN_TYPE[5:2] = Output registered, (no enable)
  // PIN_TYPE[1:0] = Simple input pin (D_IN_0)
  //
`ifndef NO_SB_IO
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
`endif

  // verilator lint_off: UNDRIVEN
  logic [SRAM_DATA_WIDTH-1:0] pad_rd_data_p1;
  // verilator lint_on: UNDRIVEN

  //
  // data (posedge output, negedge input)
  //
  // PIN_TYPE[5:2] = Output registered and enable registered
  // PIN_TYPE[1:0] = Input 'DDR' data is clocked out on rising
  //                 and falling clock edges. Use the D_IN_0
  //                 and D_IN_1 pins for DDR operation.
  //
`ifndef NO_SB_IO
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
`endif

  // oe non-neg version
  logic pad_oe_p2 = 1'b0;

  always_ff @(posedge clk) begin
    if (pad_oe_p2) begin
      pad_rd_data  <= pad_rd_data_p1;
      pad_rd_valid <= 1'b1;
    end else begin
      pad_rd_valid <= 1'b0;
    end

    pad_oe_p2 <= !pad_oe_n_p1;
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
  logic [DW-1:0] mem            [0:(1 << AW)-1];

  logic [AW-1:0] pad_addr_p1;
  logic          pad_wr_en_p1;
  logic [DW-1:0] pad_wr_data_p1;
  logic          pad_ce_n_p1;
  logic          pad_we_n_p1;
  logic          pad_oe_n_p1;

  logic [AW-1:0] pad_addr_p2;
  logic          pad_wr_en_p2;
  logic [DW-1:0] pad_wr_data_p2;
  logic          pad_ce_n_p2;
  logic          pad_we_n_p2;
  logic          pad_oe_n_p2;

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      pad_wr_en_p1 <= 1'b1;
      pad_ce_n_p1  <= 1'b1;
      pad_we_n_p1  <= 1'b1;
      pad_oe_n_p1  <= 1'b1;

      pad_wr_en_p2 <= 1'b1;
      pad_ce_n_p2  <= 1'b1;
      pad_we_n_p2  <= 1'b1;
      pad_oe_n_p2  <= 1'b1;

      pad_rd_valid <= 1'b0;
    end else begin
      pad_addr_p1    <= pad_addr;
      pad_wr_en_p1   <= pad_wr_en;
      pad_wr_data_p1 <= pad_wr_data;
      pad_ce_n_p1    <= pad_ce_n;
      pad_we_n_p1    <= pad_we_n;
      pad_oe_n_p1    <= pad_oe_n;

      pad_addr_p2    <= pad_addr_p1;
      pad_wr_en_p2   <= pad_wr_en_p1;
      pad_wr_data_p2 <= pad_wr_data_p1;
      pad_ce_n_p2    <= pad_ce_n_p1;
      pad_we_n_p2    <= pad_we_n_p1;
      pad_oe_n_p2    <= pad_oe_n_p1;

      pad_rd_valid   <= !pad_oe_n_p2;
      pad_rd_data    <= sram_io_data;
    end
  end

  // Drive SRAM signals
  assign sram_io_addr = pad_addr_p2;
  assign sram_io_we_n = pad_we_n_p2;
  assign sram_io_oe_n = pad_oe_n_p2;
  assign sram_io_ce_n = pad_ce_n_p2;

  always @(*) begin
    // verilator lint_off: ASSIGNIN
    if (pad_wr_en_p2) begin
      sram_io_data = pad_wr_data_p2;
    end else if (!pad_oe_n_p2) begin
      sram_io_data = mem[sram_io_addr];
    end else begin
      sram_io_data = 'x;
    end
    // verilator lint_on: ASSIGNIN
  end

  always @(posedge clk) begin
    // verilator lint_off: BLKSEQ
    if ($fell(sram_io_we_n)) begin
      mem[sram_io_addr] = sram_io_data;
    end
    // verilator lint_on: BLKSEQ
  end

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
