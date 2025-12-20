# Timing Closure Plan: dcache → CPU → imem Critical Path

## Constraints

- **Target**: 100 MHz (10ns clock period)
- **CPI**: Zero impact required - cache hit latency must remain unchanged
- **Approach**: One change at a time, test after each

## Critical Path Summary

```
dcache/tag_table_reg[127][0][5]/Q (STARTPOINT)
    ↓
Deep LUT6/MUXF7 chain (rd_data[31] mux tree)
    ↓
way0_hit (tag comparison)
    ↓
FSM_onehot_state (cache FSM → rd_ready)
    ↓
svc_sticky_bit_aw_i/state_reg
    ↓
dmem_stall → stall_cpu → stall_pc
    ↓
stage_id/pipe_bpred_taken
    ↓
stage_ex/pipe_payload_data
    ↓
imem_ren → imem/mem_reg_6/ENBWREN (ENDPOINT)
```

## Step-by-Step Plan

### Step 1: Add max_fanout attributes

**Files to modify:**

- `svc/rtl/common/svc_cache_axi.sv`
- `svc/rtl/rv/svc_rv_dmem_cache_if.sv`
- `svc/rtl/rv/svc_rv_stage_if_bram.sv`

**Changes:**

```systemverilog
// svc_cache_axi.sv - add to signal declarations
(* max_fanout = 16 *) logic hit;
(* max_fanout = 16 *) logic rd_ready;

// svc_rv_dmem_cache_if.sv
(* max_fanout = 16 *) logic dmem_stall;

// svc_rv_stage_if_bram.sv
(* max_fanout = 16 *) logic imem_ren;
```

**Risk**: None

**Testing:**

```bash
make format && make lint
make tb
make formal  # if applicable
```

---

### Step 2: Register imem_ren

**File:** `svc/rtl/rv/svc_rv_stage_if_bram.sv`

**Current code (line ~105-106 with BPRED):**

```systemverilog
assign imem_raddr = pc_next;
assign instr      = imem_rdata;
assign imem_ren   = !rst_n || !pc_stall;
```

**New code:**

```systemverilog
assign imem_raddr = pc_next;
assign instr      = imem_rdata;

// Register imem_ren to break timing path to BRAM enable
// BRAM 1-cycle latency absorbs this - instruction arrives same cycle relative to pipeline
logic imem_ren_reg;

always_ff @(posedge clk) begin
  if (!rst_n) begin
    imem_ren_reg <= 1'b1;  // Enable on reset for first fetch
  end else begin
    imem_ren_reg <= !pc_stall;
  end
end

assign imem_ren = imem_ren_reg;
```

**Risk**: Low - instruction buffer already handles stalled data

**Testing:**

```bash
make format && make lint
make rv_hello_sim      # verify basic functionality
make rv_blinky_sim     # verify UART output
make tb
make formal
```

---

### Step 3: Restructure dmem_stall (if still needed)

**File:** `svc/rtl/rv/svc_rv_dmem_cache_if.sv`

**Current code (line 289):**

```systemverilog
assign dmem_stall = (state_next != STATE_IDLE) || completing;
```

**New code:**

```systemverilog
// Stall when: in operation, OR starting new cache operation this cycle
// Uses registered 'state' (fast) instead of 'state_next' (slow)
logic starting_cache_op;
assign starting_cache_op = (state == STATE_IDLE) && !completing &&
                           ((dmem_ren && !io_sel_rd) || (dmem_we && !io_sel_wr));

assign dmem_stall = (state != STATE_IDLE) || completing || starting_cache_op;
```

**Risk**: Medium - changes stall timing, need careful testing

**Testing:**

```bash
make format && make lint
make rv_hello_sim
make rv_blinky_sim
make tb
make svc_rv_dmem_cache_if_f  # specific formal check
make formal
```

---

### Step 4: Further optimizations (if still needed)

Only proceed if timing still fails after Steps 1-3.

Options:

- Register `rd_ready` in cache (adds 1 cycle - violates CPI constraint)
- Pipeline tag comparison
- Pre-decode stall in CPU hazard unit

---

## Key Files Reference

| Module        | File                                 |
| ------------- | ------------------------------------ |
| dcache        | `svc/rtl/common/svc_cache_axi.sv`    |
| sticky_bit    | `svc/rtl/common/svc_sticky_bit.sv`   |
| dmem_cache_if | `svc/rtl/rv/svc_rv_dmem_cache_if.sv` |
| stage_if_bram | `svc/rtl/rv/svc_rv_stage_if_bram.sv` |
| stage_id      | `svc/rtl/rv/svc_rv_stage_id.sv`      |
| stage_ex      | `svc/rtl/rv/svc_rv_stage_ex.sv`      |

## Progress Tracking

- [ ] Step 1: max_fanout attributes
- [ ] Step 2: Register imem_ren
- [ ] Step 3: Restructure dmem_stall (if needed)
- [ ] Step 4: Further optimizations (if needed)
