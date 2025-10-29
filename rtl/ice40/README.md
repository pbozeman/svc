# iCE40 FPGA Modules

Platform-specific implementations for Lattice iCE40 FPGAs.

## Clock Generation

- **svc_ice40_pll_20.sv** - 20 MHz PLL
- **svc_ice40_pll_25.sv** - 25 MHz PLL
- **svc_ice40_pll_75.sv** - 75 MHz PLL
- **svc_ice40_vga_pll.sv** - VGA-specific PLL configuration

## VGA Support

- **svc_ice40_vga_mode.sv** - VGA mode configuration for iCE40

## SRAM Interface

- **svc_ice40_sram_io.sv** - SRAM physical interface primitives
- **svc_ice40_sram_io_if.sv** - SRAM controller interface
- **svc_ice40_axil_sram.sv** - AXI-Lite to SRAM wrapper
- **svc_ice40_axi_sram.sv** - Full AXI to SRAM wrapper

## Design Notes

These modules use iCE40-specific primitives:

- SB_PLL40_PAD for clock generation
- SB_IO for bidirectional SRAM data bus

For portability, keep platform-specific code isolated in this directory.
