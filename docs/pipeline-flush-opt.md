# Pipeline Flush Optimization Plan

## Problem Statement

Pipeline flush signals currently clear wide data buses (200-400+ bits per stage)
unnecessarily. While the RTL correctly uses synchronous reset only, Vivado maps
these synchronous clears to FDRE.R control pins, creating:

- Large combinational decode cones from flush logic
- High fanout control nets (flush drives hundreds of flip-flops)
- Timing pressure on control paths

The preferred architecture is to **drop validity** (1-bit) and let garbage data
sit, since downstream logic already gates all side effects on validity.

## Key Architectural Insight

The codebase already separates:

| Signal Type | Examples                                     | Cleared on Flush? | Width       |
| ----------- | -------------------------------------------- | ----------------- | ----------- |
| **Control** | `reg_write_*`, `mem_write_*`, `trap_*`       | YES               | 2-8 bits    |
| **Payload** | `rd_*`, `rs1_data_*`, `alu_result_*`, `pc_*` | Currently yes     | 40-400 bits |

**Every side-effect-producing operation is gated by control signals or
validity:**

```systemverilog
// Forwarding: gated by reg_write_mem
if (reg_write_mem && rd_mem != 5'd0 && ...) begin
  mem_to_ex_fwd_a = (rd_mem == rs1_ex);
end

// RAS update: gated by s_valid (via s_accept)
assign ras_push_en = s_accept && is_jmp_mem && (rd_mem != 5'b0);

// BTB update: gated by s_valid
assign btb_update_en = en && is_predictable && ...;  // en = s_valid
```

Since control signals ARE cleared on flush, payload can safely remain garbage.

## Current State

The `svc_rv_pipe_data` module clears data on both flush and bubble:

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n)      data_o <= reset_load_val;
  else if (flush)  data_o <= flush_load_val;   // Clears wide payload
  else if (bubble) data_o <= bubble_load_val;  // Clears wide payload
  else if (advance) data_o <= data_i;
end
```

**Existing mitigations:**

- Payload registers already use `.bubble(1'b0)` to skip bubble clears
- Control registers (narrow) correctly use `.bubble(pipe_bubble_o)`

**What's missing:**

- Payload registers still use `.flush(pipe_flush_o)` - clearing wide buses

## Proposed Changes

### Change Summary

| File                      | Instance             | Width     | Change                             |
| ------------------------- | -------------------- | --------- | ---------------------------------- |
| `svc_rv_stage_ex.sv`      | `pipe_payload_data`  | ~408 bits | `.flush(1'b0)`                     |
| `svc_rv_stage_ex.sv`      | `pipe_m_result_data` | 32 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_mem.sv`     | `pipe_payload_data`  | ~334 bits | `.flush(1'b0)`                     |
| `svc_rv_stage_mem.sv`     | `pipe_ld_data`       | 32 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_id.sv`      | `pipe_data_signals`  | 40 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_id.sv`      | `pipe_fwd_data`      | 64 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_id.sv`      | `pipe_imm_pc`        | 96 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_id.sv`      | `pipe_instr`         | 32 bits   | `.flush(1'b0)`, remove `FLUSH_VAL` |
| `svc_rv_stage_pc.sv`      | `pipe_payload`       | 64 bits   | `.flush(1'b0)`                     |
| `svc_rv_stage_if_bram.sv` | `instr_buf`          | 32 bits   | Remove NOP clear on flush          |
| `svc_rv_stage_if_sram.sv` | `instr_buf`          | 32 bits   | Remove NOP clear on flush          |

**Estimated reduction:** ~1000 bits no longer cleared on flush.

### Instances to Leave Unchanged

These correctly clear narrow control signals:

| File                  | Instance            | Width  | Reason                  |
| --------------------- | ------------------- | ------ | ----------------------- |
| `svc_rv_stage_ex.sv`  | `pipe_ctrl_data`    | 4 bits | Gates reg/mem write     |
| `svc_rv_stage_mem.sv` | `pipe_ctrl_data`    | 2 bits | Gates reg write, trap   |
| `svc_rv_stage_id.sv`  | `pipe_ctrl_signals` | 8 bits | Gates decoder outputs   |
| `svc_rv_stage_pc.sv`  | `pipe_ctrl_signals` | 5 bits | BTB/RAS control         |
| `svc_rv_pipe_ctrl.sv` | `valid_o`           | 1 bit  | Primary validity signal |

## Detailed Changes

### 1. `svc_rv_stage_ex.sv`

**Before:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH(PAYLOAD_WIDTH),
    .REG  (PIPELINED)
) pipe_payload_data (
    .flush(pipe_flush_o),
    .bubble(1'b0),
    // ...
);
```

**After:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH(PAYLOAD_WIDTH),
    .REG  (PIPELINED)
) pipe_payload_data (
    .flush(1'b0),          // Payload: let garbage sit
    .bubble(1'b0),
    // ...
);
```

Same change for `pipe_m_result_data`.

### 2. `svc_rv_stage_mem.sv`

**Before:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH(PAYLOAD_WIDTH),
    .REG  (PIPELINED)
) pipe_payload_data (
    .flush(pipe_flush_o),
    .bubble(1'b0),
    // ...
);
```

**After:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH(PAYLOAD_WIDTH),
    .REG  (PIPELINED)
) pipe_payload_data (
    .flush(1'b0),          // Payload: let garbage sit
    .bubble(1'b0),
    // ...
);
```

Same change for `pipe_ld_data`.

### 3. `svc_rv_stage_id.sv`

Apply `.flush(1'b0)` to:

- `pipe_data_signals`
- `pipe_fwd_data`
- `pipe_imm_pc`
- `pipe_instr` (also remove `FLUSH_VAL(I_NOP)`)

### 4. `svc_rv_stage_pc.sv`

**Before:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH     (2 * XLEN),
    .REG       (PC_REG),
    .BUBBLE_REG(1)
) pipe_payload (
    .flush  (pipe_flush),
    .bubble (pipe_bubble),
    // ...
);
```

**After:**

```systemverilog
svc_rv_pipe_data #(
    .WIDTH     (2 * XLEN),
    .REG       (PC_REG),
    .BUBBLE_REG(1)
) pipe_payload (
    .flush  (1'b0),        // BTB/RAS targets: garbage OK when invalid
    .bubble (pipe_bubble),
    // ...
);
```

### 5. `svc_rv_stage_if_bram.sv`

**Before:**

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n || if_id_flush || flush_extend) begin
    instr_buf <= I_NOP;
  end else if (advance) begin
    instr_buf <= instr;
  end
end
```

**After:**

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) begin
    instr_buf <= I_NOP;    // Only reset clears
  end else if (advance) begin
    instr_buf <= instr;
  end
  // Flush: valid_buf=0 gates downstream, garbage instruction OK
end
```

### 6. `svc_rv_stage_if_sram.sv`

Same pattern as BRAM variant.

## Verification Plan

### Formal Verification

Run existing formal checks - they should pass unchanged since functional
behavior is preserved:

```bash
make svc_rv_pipe_ctrl_f
make svc_rv_pipe_data_f
make svc_rv_stage_id_f
make svc_rv_stage_ex_f
make svc_rv_stage_mem_f
make svc_rv_stage_pc_f
make svc_rv_stage_if_f
```

### RVFI Formal

Run RISC-V Formal to verify architectural correctness:

```bash
make rv_rvfi_f
```

Note: RVFI will see garbage instruction bits when `rvfi_valid=0`. This is
spec-compliant (RVFI only requires valid data when `rvfi_valid=1`).

### Simulation

Run full testbench suite:

```bash
make quick
make full
```

## Corner Cases to Verify

### 1. Flush + Stall Same Cycle

- **Scenario:** `flush=1` and `stall=1` simultaneously
- **Expected:** Valid drops immediately, data holds until stall releases
- **Verify:** Pipeline resumes correctly after stall

### 2. Back-to-back Bubbles

- **Scenario:** Multiple consecutive data hazard bubbles
- **Expected:** Each bubble drops valid, garbage payload stable
- **Verify:** No spurious forwarding from garbage `rd_*`

### 3. Mispredict Flush + Valid Instruction in Later Stage

- **Scenario:** Branch mispredict in EX, valid instruction in MEM
- **Expected:** EX flushed (garbage), MEM completes normally
- **Verify:** MEM instruction writes correct result

### 4. Flush During Multi-cycle Operation

- **Scenario:** Flush while DIV/REM in progress (`op_active_ex=1`)
- **Expected:** Operation aborts, garbage result, `reg_write_*=0`
- **Verify:** No register file corruption

### 5. Cache Miss + Flush

- **Scenario:** `dmem_stall` active when flush asserts
- **Expected:** Stall completes, flushed instruction doesn't write
- **Verify:** Correct instruction resumes after cache fill

### 6. Forwarding with Garbage Payload

- **Scenario:** Garbage `rd_mem` accidentally matches `rs1_ex`
- **Expected:** `reg_write_mem=0` prevents forwarding
- **Verify:** Correct value used (from regfile, not garbage forward)

### 7. RAS/BTB with Garbage Payload

- **Scenario:** Garbage `is_jmp_mem`, `rd_mem` after flush
- **Expected:** `s_valid=0` prevents RAS push/pop
- **Verify:** RAS stack not corrupted

## Expected Impact

| Metric                      | Before         | After        |
| --------------------------- | -------------- | ------------ |
| Bits cleared on flush (EX)  | ~440           | 4            |
| Bits cleared on flush (MEM) | ~368           | 2            |
| Bits cleared on flush (ID)  | ~232           | 8            |
| Bits cleared on flush (IF)  | ~32            | 0            |
| **Total flush fanout**      | **~1072 bits** | **~14 bits** |

**Fanout reduction:** ~75x fewer flip-flops driven by flush.

## Implementation Order

Changes will be made **one instance at a time**, with user running tests between
each change to isolate any regressions.

### Sequence (by impact, largest first):

1. `svc_rv_stage_ex.sv:pipe_payload_data` (~408 bits)
2. `svc_rv_stage_mem.sv:pipe_payload_data` (~334 bits)
3. `svc_rv_stage_id.sv:pipe_imm_pc` (96 bits)
4. `svc_rv_stage_id.sv:pipe_fwd_data` (64 bits)
5. `svc_rv_stage_pc.sv:pipe_payload` (64 bits)
6. `svc_rv_stage_id.sv:pipe_data_signals` (40 bits)
7. `svc_rv_stage_id.sv:pipe_instr` (32 bits)
8. `svc_rv_stage_ex.sv:pipe_m_result_data` (32 bits)
9. `svc_rv_stage_mem.sv:pipe_ld_data` (32 bits)
10. `svc_rv_stage_if_bram.sv:instr_buf` (32 bits)
11. `svc_rv_stage_if_sram.sv:instr_buf` (32 bits)

### Process for each change:

1. Claude makes single change
2. User runs `make quick` (or `make full`)
3. If pass: proceed to next change
4. If fail: analyze, fix, or revert

## Rollback Plan

If issues arise, revert to `.flush(pipe_flush_o)` on affected instances. The
change is purely additive (removing clears), so rollback is trivial.
