# Graphics Modules

Graphics primitives and VGA display subsystem.

## VGA Timing and Display

- **svc_vga_mode.sv** - VGA mode configuration and timing parameters
- **svc_gfx_vga.sv** - Top-level VGA controller with framebuffer
- **svc_gfx_vga_fade.sv** - VGA fade effect
- **svc_pix_vga.sv** - Pixel-to-VGA output interface

## Framebuffer

- **svc_gfx_fb.sv** - Graphics framebuffer with AXI interface
- **svc_fb_vga.sv** - Framebuffer to VGA output
- **svc_fb_pix.sv** - Pixel write interface
- **svc_fb_pix_vga.sv** - Pixel interface with VGA output

## Graphics Primitives

- **svc_gfx_line.sv** - Bresenham line drawing
- **svc_gfx_rect_fill.sv** - Rectangle fill operation

## Clock Domain Crossing

- **svc_pix_cdc.sv** - Pixel data CDC for VGA timing domains

## Color Management

- **svc_rgb.sv** - RGB color utilities

## Integration

Graphics modules typically use:

1. Graphics primitives (line, rect) generate pixel coordinates
2. Framebuffer stores pixel data via AXI
3. VGA controller reads framebuffer and outputs video signals
