# Section 1.3 Option B: Full Revert to Pre-7f0c174e

## Overview

This plan restores the pre-unified IF stage architecture where:

- `svc_rv_stage_if.sv` is a thin wrapper with PC logic
- `svc_rv_stage_if_bram.sv` handles BRAM-specific timing (1-cycle latency)
- `svc_rv_stage_if_sram.sv` handles SRAM-specific timing (0-cycle latency)
- `svc_rv_bpred_if.sv` handles BTB/RAS signal buffering

## Key Architecture Differences

### Pre-7f0c174e (Target)

```
                    ┌─────────────────────────────────────┐
                    │         svc_rv_stage_if             │
                    │  ┌─────────────────────────────┐    │
  pc_stall ────────►│  │  PC Register + PC Next Mux │    │
  pc_sel ──────────►│  └─────────────────────────────┘    │
  pc_redirect_tgt ─►│              │                      │
  pred_tgt ────────►│              ▼                      │
                    │  ┌─────────────────────────────┐    │
                    │  │  if (MEM_TYPE == BRAM)      │    │
                    │  │    svc_rv_stage_if_bram     │    │
                    │  │  else                       │    │
                    │  │    svc_rv_stage_if_sram     │    │
                    │  └─────────────────────────────┘    │
                    │              │                      │
                    │              ▼                      │
                    │  ┌─────────────────────────────┐    │
                    │  │     svc_rv_bpred_if         │    │
                    │  │  (BTB/RAS signal buffering) │    │
                    │  └─────────────────────────────┘    │
                    └─────────────────────────────────────┘
                                   │
                                   ▼ instr_id, pc_id, btb_*, ras_*
```

Flow control: `pc_stall` gates PC register update

### Current (Post-7f0c174e + FIFOs)

```
  ┌──────────────┐     ┌─────────────────────────────────────┐
  │ svc_rv_stage │     │         svc_rv_stage_if             │
  │     _pc      │────►│  ┌─────────────────────────────┐    │
  │              │     │  │  FIFOs for PC, instr, meta  │    │
  └──────────────┘     │  └─────────────────────────────┘    │
                       │              │                      │
                       │              ▼                      │
                       │  Unified interface (imem_rvalid)    │
                       └─────────────────────────────────────┘
                                      │
                                      ▼ instr_id, pc_id, btb_*, ras_*
```

Flow control: `s_valid/s_ready` and `m_valid/m_ready` handshakes

## Files to Modify/Create

| File                            | Action  | Description                        |
| ------------------------------- | ------- | ---------------------------------- |
| `svc_rv_stage_if.sv`            | Replace | Restore wrapper with PC logic      |
| `svc_rv_stage_if_bram.sv`       | Create  | Restore BRAM fetch logic           |
| `svc_rv_stage_if_sram.sv`       | Create  | Restore SRAM fetch logic           |
| `svc_rv_bpred_if.sv`            | Create  | Restore BTB/RAS buffering          |
| `svc_rv.sv`                     | Modify  | Add MEM_TYPE to IF, restore stalls |
| `svc_rv_soc_sram.sv`            | Modify  | Remove imem hold logic             |
| `svc_rv_soc_bram.sv`            | Modify  | Minor cleanup                      |
| `svc_rv_stage_pc.sv`            | Delete  | PC logic moves back to IF          |
| `tb/formal/svc_rv_stage_if.sby` | Modify  | Update for new interface           |

## Signal Renames Required

The pre-7f0c174e code used old signal names. Apply these renames:

| Old Name             | New Name       |
| -------------------- | -------------- |
| `btb_target_*`       | `btb_tgt_*`    |
| `ras_target_*`       | `ras_tgt_*`    |
| `pc_redirect_target` | `pc_redir_tgt` |
| `pred_target`        | `pred_tgt`     |
| `load_*`             | `ld_*`         |

---

## Step-by-Step Implementation

### Step 1: None

### Step 2: Restore svc_rv_stage_if_sram.sv

Extract and rename:

```bash
git show 7f0c174e^:rtl/rv/svc_rv_stage_if_sram.sv > rtl/rv/svc_rv_stage_if_sram.sv
```

Apply renames in the file:

- `btb_target_if` → `btb_tgt_if`
- `btb_target_to_if_id` → `btb_tgt_to_if_id`
- `ras_target_if` → `ras_tgt_if`
- `ras_target_to_if_id` → `ras_tgt_to_if_id`

Key characteristics of SRAM IF:

- 0-cycle read latency (combinational)
- `imem_arvalid = 1'b1` always
- PC/BTB/RAS passthrough (no buffering needed)
- Optional instruction buffer for pipelined mode

### Step 3: Restore svc_rv_stage_if_bram.sv

Extract and rename:

```bash
git show 7f0c174e^:rtl/rv/svc_rv_stage_if_bram.sv > rtl/rv/svc_rv_stage_if_bram.sv
```

Apply same renames as Step 2.

Key characteristics of BRAM IF:

- 1-cycle read latency (registered)
- PC buffering to align with delayed instruction
- BTB/RAS buffering to match instruction timing
- `flush_extend` logic to handle flush during pending fetch

### Step 4: Restore svc_rv_bpred_if.sv

Extract and rename:

```bash
git show 7f0c174e^:rtl/rv/svc_rv_bpred_if.sv > rtl/rv/svc_rv_bpred_if.sv
```

Apply renames:

- `btb_target_*` → `btb_tgt_*`
- `ras_target_*` → `ras_tgt_*`

This module handles conditional BTB/RAS buffering:

- SRAM + pipelined: Buffer signals
- BRAM + pipelined: Passthrough (already buffered in IF_bram)
- Non-pipelined: Passthrough

### Step 5: Write new hybrid svc_rv_stage_if.sv

This is the biggest change. Write a **new hybrid version** that combines:

- Old structure (BRAM/SRAM submodule dispatch + bpred_if)
- Current interface (`s_valid/s_ready` from `stage_pc`)
- Relevant formals (basic stability, not variable latency)

#### 5a. Structure (from old)

1. Dispatches to BRAM or SRAM submodule based on MEM_TYPE
2. Instantiates svc_rv_bpred_if for BTB/RAS handling
3. Contains IF/ID pipeline registers
4. Simple PC/metadata buffering (single register, not FIFOs)

#### 5b. Interface (hybrid)

| Signal                | Source | Notes                        |
| --------------------- | ------ | ---------------------------- |
| `s_valid`, `s_ready`  | Keep   | From stage_pc                |
| `m_valid`, `m_ready`  | Keep   | To ID stage                  |
| `pc_if`, `pc_next_if` | Keep   | From stage_pc (not internal) |
| `if_id_flush`         | Keep   | Flush control                |
| `imem_rvalid`         | Remove | Not needed (fixed latency)   |

#### 5c. Formals to keep

```systemverilog
// Output stability (m_valid && !m_ready → payload stable)
`FASSERT(a_valid_stable, m_valid || f_flush);
`FASSERT(a_instr_stable, instr_id == $past(instr_id));
`FASSERT(a_pc_stable, pc_id == $past(pc_id));
// ... other payload signals

// Input stability (s_valid && !s_ready → inputs stable)
`FASSUME(a_in_pc_stable, pc_if == $past(pc_if));
// ... other input signals

// Basic cover properties
`FCOVER(c_back_to_back, $past(m_valid && m_ready) && m_valid);
`FCOVER(c_stalled, $past(m_valid && !m_ready) && m_valid && m_ready);

// imem_araddr verification
`FASSERT(a_imem_addr_bpred, imem_araddr == pc_next_if);    // BPRED mode
`FASSERT(a_imem_addr_no_bpred, imem_araddr == pc_if);      // non-BPRED
```

#### 5d. Remove (variable latency support)

- FIFOs (`pc_fifo`, `aligned_pc_fifo`, `instr_fifo`, `meta_fifo`)
- Multi-cycle latency tracking (`f_req_cycles`, `f_outstanding`)
- Stale response discard (`outstanding`, `discard_pending`)
- Shadow queue tracking for multiple outstanding requests
- Cover properties for 2/3 cycle responses

#### 5e. Signal renames (apply throughout)

- `btb_target_*` → `btb_tgt_*`
- `ras_target_*` → `ras_tgt_*`
- `pc_redirect_target` → `pc_redir_tgt`
- `pred_target` → `pred_tgt`

### Step 6: Keep svc_rv_stage_pc.sv

Keep `svc_rv_stage_pc.sv` - it helps meet timing by separating PC logic from IF
stage. The IF stage will receive PC values from stage_pc rather than managing
the PC register internally.

### Step 7: Update svc_rv.sv

Major changes needed:

#### 7a. Update includes

```systemverilog
// Add back
`include "svc_rv_bpred_if.sv"
`include "svc_rv_stage_if_sram.sv"
`include "svc_rv_stage_if_bram.sv"

// Keep svc_rv_stage_pc.sv include (helps timing)
```

#### 7b. Remove imem_rvalid from port list

```systemverilog
// Remove this line from module ports:
// input  logic        imem_rvalid,
```

#### 7c. Remove stage_pc instantiation

Delete the entire `svc_rv_stage_pc` instantiation block.

#### 7d. Update stage_if instantiation

```systemverilog
svc_rv_stage_if #(
    .XLEN     (XLEN),
    .PIPELINED(PIPELINED),
    .MEM_TYPE (MEM_TYPE),           // Add back
    .BPRED    (BPRED),
    .RESET_PC (RESET_PC)
) stage_if (
    .clk              (clk),
    .rst_n            (rst_n),
    .pc_stall         (pc_stall),      // Restore
    .if_id_flush      (if_id_flush),
    .pc_sel           (pc_sel),        // Restore
    .pc_redir_tgt     (pc_redir_tgt),  // Restore (renamed)
    .pred_tgt         (pred_tgt_id),   // Restore (renamed)
    .btb_hit_if       (btb_hit_if),
    .btb_pred_taken_if(btb_pred_taken_if),
    .btb_tgt_if       (btb_tgt_if),
    .btb_is_return_if (btb_is_return_if),
    .ras_valid_if     (ras_valid_if),
    .ras_tgt_if       (ras_tgt_if),
    .imem_arvalid     (imem_arvalid),
    .imem_araddr      (imem_araddr),
    .imem_rdata       (imem_rdata),
    .pc               (pc_if),         // Output for BTB
    .instr_id         (instr_id),
    .pc_id            (pc_id),
    .pc_plus4_id      (pc_plus4_id),
    .btb_hit_id       (btb_hit_id),
    .btb_pred_taken_id(btb_pred_taken_id),
    .btb_tgt_id       (btb_tgt_id),
    .btb_is_return_id (btb_is_return_id),
    .ras_valid_id     (ras_valid_id),
    .ras_tgt_id       (ras_tgt_id),
    .m_valid          (if_m_valid),
    .m_ready          (if_m_ready)
);
```

#### 7e. Restore stall logic

The pre-7f0c174e stall logic was simpler:

```systemverilog
// Pipelined mode stalls
assign pc_stall    = data_hazard_id || op_active_ex || halt_next || halt;
assign id_stall    = data_hazard_id || op_active_ex || halt_next || halt;
```

### Step 8: Update svc_rv_soc_sram.sv

Remove the imem hold logic since SRAM IF handles its own timing:

```systemverilog
// Remove these signal declarations:
// logic        imem_arvalid;
// logic        imem_rvalid;

// Remove g_pipelined_imem block entirely (the hold register and rvalid logic)

// Change:
//   assign imem_rdata = imem_rdata_hold;  (pipelined)
//   assign imem_rdata = imem_rdata_sram;  (single-cycle)
// To:
assign imem_rdata = imem_rdata_sram;  // Direct connection

// In cpu instantiation, revert to old unconnected style:
//   .imem_arvalid(),      // Leave unconnected (was connected)
//   // Remove .imem_rvalid() entirely (signal removed from CPU)
```

### Step 9: Update svc_rv_soc_bram.sv

Remove imem_rvalid:

```systemverilog
// Remove imem_rvalid signal declaration
// Remove imem_rvalid logic (if any)
// In cpu instantiation:
//   .imem_arvalid(),      // Leave unconnected
//   // Remove .imem_rvalid() entirely
```

### Step 10: Format and Lint

```bash
make format
make lint
```

---

## Testing Sequence

### Phase 1: Basic Compilation

```bash
make lint
```

Fix any syntax/connection errors.

### Phase 2: Individual Testbenches

```bash
# BRAM variants
make svc_rv_soc_bram_tb
make svc_rv_soc_bram_fwd_tb

# SRAM variants
make svc_rv_soc_sram_tb
make svc_rv_soc_sram_fwd_tb
```

### Phase 3: Full Testbench Suite

```bash
make tb
```

### Phase 4: Formal Verification

Update `tb/formal/svc_rv_stage_if.sby` for new interface, then:

```bash
make svc_rv_stage_if_f
make formal
```

### Phase 5: RISC-V Formal

```bash
# Run riscv-formal checks
cd tb/riscv-formal/cores/svc_rv
make
```

### Phase 6: CPI Benchmarks

Compare CPI before/after:

```bash
# Run with SVC_TB_RPT=1 for CPI reporting
SVC_TB_RPT=1 make svc_rv_soc_bram_tb
SVC_TB_RPT=1 make svc_rv_soc_sram_tb
```

---

## Rollback Plan

If issues arise, revert to the FIFO-based unified IF:

```bash
git checkout main -- rtl/rv/svc_rv_stage_if.sv
git checkout main -- rtl/rv/svc_rv.sv
git checkout main -- rtl/rv/svc_rv_soc_sram.sv
rm rtl/rv/svc_rv_stage_if_bram.sv
rm rtl/rv/svc_rv_stage_if_sram.sv
rm rtl/rv/svc_rv_bpred_if.sv
```

---

## Checklist

- [ ] Create branch `if-full-revert`
- [ ] Restore `svc_rv_stage_if_sram.sv` with renames
- [ ] Restore `svc_rv_stage_if_bram.sv` with renames
- [ ] Restore `svc_rv_bpred_if.sv` with renames
- [ ] Replace `svc_rv_stage_if.sv` with wrapper version
- [ ] Keep `svc_rv_stage_pc.sv` (helps timing)
- [ ] Update `svc_rv.sv` includes
- [ ] Update `svc_rv.sv` port list (remove `imem_rvalid`)
- [ ] Update `svc_rv.sv` stage_if instantiation
- [ ] Update `svc_rv.sv` stall logic
- [ ] Update `svc_rv_soc_sram.sv` (remove hold logic)
- [ ] Update `svc_rv_soc_bram.sv` (remove rvalid if present)
- [ ] `make format`
- [ ] `make lint`
- [ ] `make svc_rv_soc_bram_tb`
- [ ] `make svc_rv_soc_sram_tb`
- [ ] `make tb`
- [ ] Update formal verification
- [ ] `make formal`
- [ ] riscv-formal
- [ ] CPI benchmark comparison
