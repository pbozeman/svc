# AXI Modules

AXI and AXI-Lite bus protocol implementations.

## Bus Infrastructure

### Arbitration

- **svc_axi_arbiter.sv** - Full AXI arbiter
- **svc_axi_arbiter_rd.sv** - Read channel arbiter
- **svc_axi_arbiter_wr.sv** - Write channel arbiter

### Routing

- **svc_axil_router.sv** - AXI-Lite router
- **svc_axil_router_rd.sv** - Read channel router
- **svc_axil_router_wr.sv** - Write channel router

### Address Striping

- **svc_axi_stripe.sv** - Address-based striping across subordinates
- **svc_axi_stripe_ax.sv** - Address channel striping
- **svc_axi_stripe_rd.sv** - Read channel striping
- **svc_axi_stripe_wr.sv** - Write channel striping

## Protocol Conversion

### AXI to AXI-Lite

- **svc_axi_axil_adapter.sv** - Full adapter
- **svc_axi_axil_adapter_rd.sv** - Read channel adapter
- **svc_axi_axil_adapter_wr.sv** - Write channel adapter

### Burst Handling

- **svc_axi_burst_adapter.sv** - Burst adapter
- **svc_axi_burst_adapter_rd.sv** - Read burst adapter
- **svc_axi_burst_adapter_wr.sv** - Write burst adapter
- **svc_axi_burst_iter_ax.sv** - Burst iterator

### Reflection (Loopback)

- **svc_axi_axil_reflect_rd.sv** - Read reflection
- **svc_axi_axil_reflect_wr.sv** - Write reflection

## Memory Controllers

- **svc_axi_mem.sv** - AXI memory controller
- **svc_axil_sram_if.sv** - AXI-Lite SRAM interface
- **svc_axil_regfile.sv** - AXI-Lite register file

## Utilities

### Null/Sink

- **svc_axi_null.sv** - Full AXI sink
- **svc_axi_null_rd.sv** - Read channel sink
- **svc_axi_null_wr.sv** - Write channel sink

### Traffic Generation

- **svc_axi_tgen.sv** - Traffic generator
- **svc_axi_tgen_csr.sv** - Control/status registers
- **svc_axi_tgen_rd.sv** - Read generator
- **svc_axi_tgen_wr.sv** - Write generator

### Diagnostics

- **svc_axi_stats.sv** - Bus statistics collector
- **svc_axil_invalid_rd.sv** - Invalid read detector
- **svc_axil_invalid_wr.sv** - Invalid write detector

### UART Bridge

- **svc_axil_bridge_uart.sv** - UART to AXI-Lite bridge

## Integration Examples

Most modules follow split read/write architecture, with separate modules
handling each direction independently.
