# Clock Domain Crossing (CDC) Modules

Primitives for safe clock domain crossing.

## Modules

- **svc_cdc_sync2.sv** - Two-stage synchronizer
- **svc_cdc_fifo.sv** - Asynchronous FIFO with Gray code pointers
- **svc_cdc_fifo_mem.sv** - FIFO memory array
- **svc_cdc_fifo_rptr_empty.sv** - Read pointer and empty flag generation
- **svc_cdc_fifo_wptr_full.sv** - Write pointer and full flag generation

## Design Notes

- Uses Gray code for pointer synchronization
- Two-stage synchronization for metastability protection
- First-Word Fall-Through (FWFT) read interface

## Reference

The async FIFO implementation is based on the Sunburst Design paper:

Clifford E. Cummings, "Simulation and Synthesis Techniques for Asynchronous FIFO
Design", SNUG 2002 (Synopsys Users Group Conference, San Jose, CA, 2002)

Available at: http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
