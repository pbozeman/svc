# FIFO Modules

Synchronous FIFO implementations with various configurations.

## Modules

### Standard FIFOs

- **svc_sync_fifo.sv** - Base FWFT FIFO (depth = 2^ADDR_WIDTH)
- **svc_sync_fifo_n.sv** - FWFT FIFO with minimum depth N
- **svc_sync_fifo_n1.sv** - Optimized single-element FWFT FIFO

### Zero-Latency FIFOs

- **svc_sync_fifo_zl.sv** - Zero-latency FIFO (depth = 2^ADDR_WIDTH)
- **svc_sync_fifo_zl1.sv** - Optimized single-element zero-latency FIFO

## FIFO Variants

### FWFT (First-Word Fall-Through)

- Read data available immediately when not empty
- One cycle latency from write to read data availability

### Zero-Latency

- Read data available combinationally in same cycle as write
- Useful for tight timing constraints

## Interface

All FIFOs use common interface:

- **Write**: `w_inc`, `w_data`, `w_full`, `w_half_full`
- **Read**: `r_inc`, `r_data`, `r_empty`
