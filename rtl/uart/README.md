# UART Modules

Serial communication (UART) implementation.

## Core Modules

- **svc_uart_tx.sv** - UART transmitter
- **svc_uart_rx.sv** - UART receiver
- **svc_uart_baud_gen.sv** - Baud rate generator

## Utilities

- **svc_print.sv** - Formatted printing over UART

## Configuration

Baud rate is configurable via clock divider calculation. Standard 8N1 format (8
data bits, no parity, 1 stop bit).

## Integration

Typical usage:

1. Configure baud rate generator
2. Connect TX/RX to physical pins
3. Use print module for debugging output
