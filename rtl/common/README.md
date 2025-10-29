# Common Modules

Fundamental building blocks used throughout the SVC library.

## Modules

### Arbitration

- **svc_arbiter.sv** - Round-robin arbiter for multiple requesters
- **svc_priority_encoder.sv** - Priority encoder converting one-hot to binary

### Timing and Synchronization

- **svc_delay.sv** - Configurable cycle delay
- **svc_edge_rose.sv** - Rising edge detector
- **svc_edge_fell.sv** - Falling edge detector
- **svc_init.sv** - Initialization pulse generator

### Data Path

- **svc_skidbuf.sv** - Skid buffer for backpressure handling
- **svc_accumulator.sv** - Accumulator with saturation
- **svc_sticky_bit.sv** - Sticky bit register

### Formatting and Utilities

- **svc_hex_fmt.sv** - Hexadecimal formatter
- **svc_hex_fmt_stream.sv** - Streaming hex formatter
- **svc_str_iter.sv** - String iterator

### Testing

- **svc_unit.sv** - Lightweight testing framework
- **svc_unused.sv** - Unused signal handling macro
