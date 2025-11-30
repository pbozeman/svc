#!/usr/bin/env python3
#
# Generate a trace replay testbench from a riscv-formal check directory.
#
# Parses the config.sby to extract svc_rv parameters and the VCD trace to
# extract instruction memory accesses. Generates a SystemVerilog testbench
# that replays those accesses using case statements (compatible with iverilog).
#
# Output is written to tb/rv/<name>.sv relative to the script's location,
# so the script can be run from any directory.
#
# Usage:
#   ./scripts/rvf_to_tb.py <check_dir>
#
# Example:
#   ./scripts/rvf_to_tb.py path/to/insn_add_ch0
#   # Creates tb/rv/svc_rvf_<config>_insn_add_ch0_tb.sv
#

import argparse
import re
import sys
from pathlib import Path

from jinja2 import Environment, FileSystemLoader
from Verilog_VCD.Verilog_VCD import parse_vcd

SCRIPT_DIR = Path(__file__).parent.resolve()
REPO_ROOT = SCRIPT_DIR.parent
TEMPLATE_DIR = SCRIPT_DIR / "templates"
TB_DIR = REPO_ROOT / "tb" / "rv"

#
# Default svc_rv parameters
#
DEFAULT_PARAMS = {
    "pipelined": 1,
    "fwd": 0,
    "fwd_regfile": 1,
    "mem_type": 0,
    "bpred": 0,
    "btb_enable": 0,
    "ras_enable": 0,
    "ext_m": 0,
    "ext_zmmul": 0,
}


def extract_params_from_sby(sby_file):
    """Extract SVC_RV_v parameters from config.sby file."""
    params = DEFAULT_PARAMS.copy()

    content = sby_file.read_text()

    #
    # Look for `define SVC_RV_* patterns
    #
    pattern = r"`define\s+SVC_RV_(\w+)\s+(\d+)"
    for match in re.finditer(pattern, content):
        name = match.group(1).lower()
        value = int(match.group(2))
        if name in params:
            params[name] = value

    return params


def extract_init_from_trace_tb(trace_tb_file):
    """Extract initialization assignments from trace_tb.v."""
    content = trace_tb_file.read_text()
    init_state = []

    #
    # Known enum types - use force/release to assign
    #
    FORCE_SIGNALS = {
        "stage_ex.mc_state",
    }

    #
    # Signals to skip - these are controlled by reset or other logic
    #
    SKIP_SIGNALS = {
        "halt",
        "rvfi_halt",
    }

    #
    # Match: UUT.wrapper.dut.path = WIDTH'bVALUE;
    #
    pattern = r"UUT\.wrapper\.dut\.(\S+)\s*=\s*(\d+)'b([01]+);"
    for match in re.finditer(pattern, content):
        path = match.group(1)
        width = int(match.group(2))
        val = int(match.group(3), 2)

        #
        # Convert regfile index from 5'bXXXXX to decimal
        #
        if "regfile.regs[" in path:
            idx_match = re.search(r"regs\[5'b([01]+)\]", path)
            if idx_match:
                idx = int(idx_match.group(1), 2)
                path = re.sub(r"regs\[5'b[01]+\]", f"regs[{idx}]", path)

        #
        # Skip signals that shouldn't be initialized
        #
        if path in SKIP_SIGNALS:
            continue

        #
        # Check if this signal needs force/release (enum types)
        #
        use_force = path in FORCE_SIGNALS

        init_state.append((path, val, width, use_force))

    return init_state


def extract_imem_from_vcd(vcd_file):
    """Extract instruction memory from VCD file.

    Sample imem_raddr and imem_rdata at each timestep when imem_ren=1.
    This gives us the actual {addr -> data} mapping used in the formal trace.
    """
    vcd = parse_vcd(str(vcd_file))

    wrapper_signals = {}
    for netinfo in vcd.values():
        for net in netinfo["nets"]:
            if net["hier"] == "rvfi_testbench.wrapper":
                wrapper_signals[net["name"]] = netinfo["tv"]

    def get_val_at_time(tv, t):
        result = None
        for time, val in tv:
            if time <= t:
                result = val
            else:
                break
        return result

    imem_ren = wrapper_signals.get("imem_ren", [])
    imem_raddr = wrapper_signals.get("imem_raddr", [])
    imem_rdata = wrapper_signals.get("imem_rdata", [])

    #
    # Find max time in VCD
    #
    max_time = 0
    for tv in [imem_ren, imem_raddr, imem_rdata]:
        if tv:
            max_time = max(max_time, tv[-1][0])

    #
    # Sample at each 10ns timestep (clock period)
    #
    imem = {}
    for t in range(0, max_time + 10, 10):
        ren = get_val_at_time(imem_ren, t)
        addr = get_val_at_time(imem_raddr, t)
        data = get_val_at_time(imem_rdata, t)

        if (
            ren == "1"
            and addr
            and data
            and "x" not in addr.lower()
            and "x" not in data.lower()
        ):
            addr_int = int(addr, 2)
            data_int = int(data, 2)
            imem[addr_int] = data_int

    return imem


def extract_dmem_from_trace_tb(trace_tb_file):
    """Extract per-cycle data memory values from trace_tb.v.

    The formal tool provides UUT.dmem_rdata_any per cycle.
    Returns a dict mapping cycle number to dmem value.
    """
    content = trace_tb_file.read_text()
    dmem_per_cycle = {}

    #
    # Match: if (cycle == N) begin ... UUT.dmem_rdata_any <= 32'bXXXX;
    # We need to find the cycle number and the corresponding dmem value
    #
    # First, extract cycle blocks
    #
    cycle_pattern = (
        r"if \(cycle == (\d+)\) begin.*?UUT\.dmem_rdata_any\s*<=?\s*32'b([01]+);"
    )
    for match in re.finditer(cycle_pattern, content, re.DOTALL):
        cycle = int(match.group(1))
        val = int(match.group(2), 2)
        dmem_per_cycle[cycle] = val

    #
    # Also check the initial block for dmem_rdata_any = (not <=)
    #
    init_pattern = r"^\s+UUT\.dmem_rdata_any\s*=\s*32'b([01]+);"
    for match in re.finditer(init_pattern, content, re.MULTILINE):
        val = int(match.group(1), 2)
        #
        # Initial value applies at cycle -1 (before first cycle)
        #
        dmem_per_cycle[-1] = val

    return dmem_per_cycle


def extract_from_vcd(vcd_file):
    """Extract instruction memory and spec assertions from VCD file."""
    vcd = parse_vcd(str(vcd_file))

    #
    # Build signal lookup tables
    #
    wrapper_signals = {}
    checker_signals = {}

    for netinfo in vcd.values():
        for net in netinfo["nets"]:
            if net["hier"] == "rvfi_testbench.wrapper":
                wrapper_signals[net["name"]] = netinfo["tv"]
            elif net["hier"] == "rvfi_testbench.checker_inst":
                checker_signals[net["name"]] = netinfo["tv"]

    #
    # Extract instruction memory
    #
    imem_ren = wrapper_signals.get("imem_ren")
    imem_raddr = wrapper_signals.get("imem_raddr")
    imem_rdata = wrapper_signals.get("imem_rdata")

    assert imem_ren is not None, "imem_ren not found in VCD"
    assert imem_raddr is not None, "imem_raddr not found in VCD"
    assert imem_rdata is not None, "imem_rdata not found in VCD"

    prog = dict()
    for tv_ren, tv_addr, tv_data in zip(imem_ren, imem_raddr, imem_rdata):
        if (
            tv_ren[1] == "1"
            and "x" not in tv_addr[1].lower()
            and "x" not in tv_data[1].lower()
        ):
            addr = int(tv_addr[1], 2)
            insn = int(tv_data[1], 2)
            prog[addr] = insn

    #
    # Extract data memory reads
    #
    dmem_ren = wrapper_signals.get("dmem_ren")
    dmem_raddr = wrapper_signals.get("dmem_raddr")
    dmem_rdata = wrapper_signals.get("dmem_rdata")

    dmem = dict()
    if dmem_ren and dmem_raddr and dmem_rdata:
        for tv_ren, tv_addr, tv_data in zip(dmem_ren, dmem_raddr, dmem_rdata):
            if (
                tv_ren[1] == "1"
                and "x" not in tv_addr[1].lower()
                and "x" not in tv_data[1].lower()
            ):
                addr = int(tv_addr[1], 2)
                data = int(tv_data[1], 2)
                dmem[addr] = data

    #
    # Extract spec assertions at times when spec_valid=1
    #
    spec_valid = checker_signals.get("spec_valid", [])
    rvfi_order = wrapper_signals.get("rvfi_order", [])
    spec_names = [
        "spec_pc_wdata",
        "spec_rd_addr",
        "spec_rd_wdata",
        "spec_trap",
    ]

    def get_value_at_time(signal_tv, t):
        """Get signal value at time t (or most recent before t)."""
        result = None
        for time, val in signal_tv:
            if time <= t:
                result = val
            else:
                break
        return result

    spec_checks = []
    for t, valid in spec_valid:
        if valid == "1":
            #
            # Use rvfi_order (instruction ordinal) instead of cycle count
            #
            order_val = get_value_at_time(rvfi_order, t)
            if order_val and "x" not in order_val.lower():
                order = int(order_val, 2)
            else:
                order = t // 10
            check = {"order": order}
            for name in spec_names:
                tv = checker_signals.get(name, [])
                val = get_value_at_time(tv, t)
                if val and "x" not in val.lower():
                    check[name] = int(val, 2)
            spec_checks.append(check)

    return prog, dmem, spec_checks


def generate_testbench(
    prog, dmem_per_cycle, spec_checks, init_state, name, max_cycles, params
):
    """Generate SystemVerilog testbench using Jinja2 template."""
    env = Environment(
        loader=FileSystemLoader(TEMPLATE_DIR),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    template = env.get_template("svc_rvf_tb.sv.j2")

    #
    # Convert prog dict to sorted list of (addr, insn) tuples
    #
    imem = [(addr, insn) for addr, insn in sorted(prog.items())]

    #
    # Convert dmem_per_cycle dict to sorted list of (cycle, data) tuples
    #
    dmem = [
        (cycle, data) for cycle, data in sorted(dmem_per_cycle.items()) if cycle >= 0
    ]

    #
    # Get initial dmem value (cycle -1)
    #
    dmem_init = dmem_per_cycle.get(-1, 0)

    #
    # Sort init_state by path for consistent output
    #
    state = sorted(init_state, key=lambda x: x[0])

    return template.render(
        name=name,
        max_cycles=max_cycles,
        test_timeout=max_cycles + 100,
        imem=imem,
        dmem=dmem,
        dmem_init=dmem_init,
        spec_checks=spec_checks,
        init_state=state,
        **params,
    )


def main():
    parser = argparse.ArgumentParser(
        description="Generate trace replay testbench from riscv-formal check directory"
    )
    parser.add_argument(
        "check_dir",
        help="riscv-formal check directory (contains config.sby and engine_0/)",
    )
    parser.add_argument(
        "--name", default=None, help="Testbench module name (default: from dir name)"
    )
    parser.add_argument("--cycles", type=int, default=1000, help="Max cycles to run")

    args = parser.parse_args()

    check_dir = Path(args.check_dir)
    if not check_dir.is_dir():
        print(f"Error: {check_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    sby_file = check_dir / "config.sby"
    vcd_file = check_dir / "engine_0" / "trace.vcd"
    trace_tb_file = check_dir / "engine_0" / "trace_tb.v"

    if not sby_file.exists():
        print(f"Error: {sby_file} not found", file=sys.stderr)
        sys.exit(1)

    if not vcd_file.exists():
        print(f"Error: {vcd_file} not found", file=sys.stderr)
        sys.exit(1)

    if not trace_tb_file.exists():
        print(f"Error: {trace_tb_file} not found", file=sys.stderr)
        sys.exit(1)

    #
    # Extract parameters from config.sby
    #
    params = extract_params_from_sby(sby_file)
    print(f"# Parameters from {sby_file.name}:", file=sys.stderr)
    for k, v in params.items():
        print(f"#   {k}: {v}", file=sys.stderr)

    #
    # Extract instruction memory from VCD (shows actual fetched values)
    #
    prog = extract_imem_from_vcd(vcd_file)
    if not prog:
        print("Error: No instruction memory found in VCD", file=sys.stderr)
        sys.exit(1)
    print(f"# Extracted {len(prog)} instruction addresses from VCD", file=sys.stderr)

    #
    # Extract per-cycle dmem values from trace_tb.v
    #
    dmem_per_cycle = extract_dmem_from_trace_tb(trace_tb_file)
    print(
        f"# Extracted {len(dmem_per_cycle)} per-cycle dmem values from trace_tb.v",
        file=sys.stderr,
    )

    #
    # Extract spec checks from VCD (need timing info)
    #
    _, _, spec_checks = extract_from_vcd(vcd_file)
    print(f"# Extracted {len(spec_checks)} spec checks from VCD", file=sys.stderr)

    #
    # Extract initial state from trace_tb.v (generated by formal tool)
    #
    init_state = extract_init_from_trace_tb(trace_tb_file)
    print(
        f"# Extracted {len(init_state)} initial state values from trace_tb.v",
        file=sys.stderr,
    )

    #
    # Generate testbench name from directory structure
    # e.g., bram_bpred_fwd_checks/insn_sub_ch0 -> bram_bpred_fwd_insn_sub
    #
    if args.name:
        name = args.name
    else:
        parent = check_dir.parent.name.replace("_checks", "")
        check = check_dir.name.replace("_ch0", "")
        name = f"svc_rvf_{parent}_{check}_tb"
    tb = generate_testbench(
        prog, dmem_per_cycle, spec_checks, init_state, name, args.cycles, params
    )

    #
    # Write to tb/rv/<name>.sv
    #
    output_file = TB_DIR / f"{name}.sv"
    output_file.write_text(tb)
    print(f"# Written to {output_file}\n", file=sys.stderr)
    print(f"make {name}", file=sys.stderr)
    print(f"make {name} SVC_RV_DBG_CPU=1 | rv_colorize", file=sys.stderr)


if __name__ == "__main__":
    main()
