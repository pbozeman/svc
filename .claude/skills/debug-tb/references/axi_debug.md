# AXI/AXI-Lite Debugging Patterns

## AXI Handshake Issues

### Write Channel Deadlock

Symptoms:
- `awvalid` asserted but `awready` never responds
- `wvalid` asserted but `wready` never responds
- `bready` not asserted when `bvalid` comes

Causes:
- Subordinate expects AW before W (or vice versa)
- Missing `bready` initialization
- Arbiter stuck waiting for other channel

Fix pattern:
```systemverilog
always_ff @(posedge clk) begin
  if (~rst_n) begin
    m_axi_awvalid <= 1'b0;
    m_axi_wvalid  <= 1'b0;
    m_axi_bready  <= 1'b1;  // Always ready for response
  end
end
```

### Read Channel Deadlock

Symptoms:
- `arvalid` asserted but `arready` never responds
- `rready` not asserted when `rvalid` comes

Causes:
- Missing `rready` initialization
- Subordinate waiting for address phase to complete

Fix pattern:
```systemverilog
always_ff @(posedge clk) begin
  if (~rst_n) begin
    m_axi_arvalid <= 1'b0;
    m_axi_rready  <= 1'b1;  // Always ready for data
  end
end
```

## AXI-Lite Specific

### Response Code Errors

Check `bresp` and `rresp` for:
- `2'b00` (OKAY) - Success
- `2'b10` (SLVERR) - Subordinate error
- `2'b11` (DECERR) - Decode error (address not mapped)

### Address Alignment

AXI-Lite requires aligned accesses:
- 32-bit: Address must be 4-byte aligned (addr[1:0] == 0)
- 64-bit: Address must be 8-byte aligned (addr[2:0] == 0)

## Burst Transactions

### Burst Length Mismatch

Symptoms:
- Fewer beats received than expected
- Extra beats cause protocol violation

Check:
- `awlen`/`arlen` matches actual beat count - 1
- Wrap bursts have power-of-2 length
- Fixed bursts don't cross 4KB boundary

### Strobe Issues

`wstrb` controls which bytes are written:
- Must be contiguous for unaligned start
- Must match data width

## Common Test Patterns

### Single Write
```systemverilog
m_axi_awaddr  = addr;
m_axi_awvalid = 1'b1;
m_axi_wdata   = data;
m_axi_wstrb   = '1;
m_axi_wvalid  = 1'b1;
`TICK(clk);
`CHECK_WAIT_FOR(clk, m_axi_awready && m_axi_wready, 10);
m_axi_awvalid = 1'b0;
m_axi_wvalid  = 1'b0;
`CHECK_WAIT_FOR(clk, m_axi_bvalid, 10);
`CHECK_EQ(m_axi_bresp, 2'b00);
```

### Single Read
```systemverilog
m_axi_araddr  = addr;
m_axi_arvalid = 1'b1;
`TICK(clk);
`CHECK_WAIT_FOR(clk, m_axi_arready, 10);
m_axi_arvalid = 1'b0;
`CHECK_WAIT_FOR(clk, m_axi_rvalid, 10);
`CHECK_EQ(m_axi_rdata, expected);
`CHECK_EQ(m_axi_rresp, 2'b00);
```
