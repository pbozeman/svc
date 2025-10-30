# TODO: Registered Instruction Memory Support

## Background

The RISC-V core currently supports both registered and unregistered instruction
memory via the `IMEM_REGISTERED` parameter. When `IMEM_REGISTERED=1`, the
instruction memory output is registered to infer Block RAM, adding 1 cycle of
latency. This creates a simple 2-stage pipeline but introduces control hazards
that must be handled.

## Issues with Registered IMEM

When IMEM is registered, three pipeline hazards occur:

### 1. PC Mismatch for Jump/Branch Targets

**Problem:** By the time an instruction arrives from registered IMEM, the PC has
already advanced to the next address. For JAL/JALR/branch instructions, the jump
target calculation uses the wrong PC.

**Example:**

```
Address 0x00: JAL x1, 12  // Jump to PC + 12
```

With registered IMEM:

- Cycle 0: PC=0, fetch JAL
- Cycle 1: PC=4, JAL arrives, but `jb_target = PC + imm = 4 + 12 = 16` (wrong!)

**Solution Implemented:** Track the instruction's PC separately:

```systemverilog
if (IMEM_REGISTERED) begin : gen_instr_pc_reg
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      instr_pc <= '0;
    end else begin
      instr_pc <= pc;
    end
  end
end else begin : gen_instr_pc_comb
  assign instr_pc = pc;
end

assign jb_target = instr_pc + imm;  // Use instruction's PC, not current PC
```

### 2. Pipeline Flush After Control Flow Changes

**Problem:** When a jump/branch is taken, the next instruction has already been
fetched from the wrong address and must be flushed.

**Example:**

```
Address 0x00: JAL x1, 12  // Jump to 0x0C
Address 0x04: NOP         // Should be skipped
Address 0x0C: EBREAK      // Jump target
```

With registered IMEM:

- Cycle 1: JAL executes, PC jumps to 0x0C, but fetch from 0x04 is in progress
- Cycle 2: NOP from 0x04 arrives (wrong instruction - should be flushed!)

**Solution Implemented:** Flush (convert to NOP) when `pc_sel` was asserted:

```systemverilog
if (IMEM_REGISTERED) begin : gen_flush
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc_sel_p1 <= 1'b0;
    end else begin
      pc_sel_p1 <= pc_sel;
    end
  end

  // Convert to NOP (ADDI x0, x0, 0) if previous cycle had control flow change
  assign instr = pc_sel_p1 ? 32'h00000013 : instr_raw;
end
```

### 3. Data Hazards (Not Yet Addressed)

**Problem:** With registered IMEM, load-use and ALU-use data hazards become
visible because instructions execute in different cycles.

**Example:**

```
ADDI x1, x0, 10   // x1 = 10
ADDI x2, x1, 5    // x2 = x1 + 5 (needs x1 from previous instruction)
```

With registered IMEM:

- Cycle 1: First ADDI executes, x1 is written
- Cycle 2: Second ADDI reads x1 - **may read stale value** depending on register
  file timing

## Proper Solution: Hazard Detection Unit

The current implementation handles control hazards with simple pipeline flushes,
but this is incomplete. A proper solution requires:

1. **Hazard Detection Unit** to detect:

   - Load-use hazards (load followed by use of loaded value)
   - ALU-use hazards (back-to-back dependent instructions)
   - Control hazards (already handled with flush)

2. **Forwarding/Bypassing** to forward results from later pipeline stages back
   to earlier stages, eliminating stalls for ALU-use hazards

3. **Pipeline Stalls** when forwarding cannot resolve the hazard (e.g.,
   load-use)

## Current Status

- **Implemented:** Control hazard handling (PC tracking + flush)
- **Not Implemented:** Data hazard detection and forwarding
- **Decision:** Revert registered IMEM support until proper hazard unit is
  implemented

## Files Modified (To Be Reverted)

- `rtl/rv/svc_rv.sv` - Added `instr_pc`, `pc_sel_p1`, flush logic
- `tb/rv/svc_rv_tb.sv` - Changed to `IMEM_REGISTERED=1` for testing

## When Implementing Hazard Unit

1. Design hazard detection logic to identify:

   - RAW (Read After Write) hazards
   - Load-use hazards specifically (require stall)
   - Control hazards (already handled)

2. Add forwarding paths:

   - EX -> EX forwarding (ALU result to ALU input)
   - MEM -> EX forwarding (memory data to ALU input)

3. Add pipeline control:

   - Stall signal to freeze fetch/decode stages
   - Flush signal for control hazards (already implemented)
   - Enable signals for pipeline registers

4. Re-enable registered IMEM support with comprehensive tests:
   - Back-to-back ALU operations with dependencies
   - Load-use sequences
   - Branches after loads
   - Complex dependency chains

## References

- Patterson & Hennessy, "Computer Organization and Design", Chapter 4
- RISC-V Unprivileged ISA Specification
- Current implementation: See git history for registered IMEM changes
