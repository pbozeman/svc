# SVC RISC-V riscv-dv Verification Makefile
#
# This Makefile orchestrates the full riscv-dv verification flow:
# 1. Generate random tests using riscv-dv
# 2. Compile tests with RISC-V GCC
# 3. Run tests on Spike (reference ISS)
# 4. Run tests on Verilator RTL simulation
# 5. Compare traces
#
# Prerequisites:
# - Python 3 with pyyaml
# - RISC-V GCC toolchain (riscv32-unknown-elf-gcc)
# - Spike RISC-V ISS
# - Verilator

# Directories
TOP_DIR := $(shell cd ../.. && pwd)
RISCV_DV_DIR := $(CURDIR)/riscv-dv
TARGET_DIR := $(CURDIR)/target/svc_rv
RTL_SIM_DIR := $(CURDIR)/rtl_sim
OUT_DIR := $(CURDIR)/out
BUILD_DIR := $(TOP_DIR)/.build/riscv-dv

# NixOS compatibility - export BASH path for riscv-dv
export BASH := $(shell which bash)

# Tools
PYTHON := python3
RISCV_GCC := riscv64-none-elf-gcc
RISCV_OBJCOPY := riscv64-none-elf-objcopy
SPIKE := spike

# Settings
ISA := rv32im_zicsr
ABI := ilp32
ITERATIONS := 1
MAX_CYCLES := 1000000

# GCC flags
GCC_FLAGS := -march=$(ISA) -mabi=$(ABI) -static -mcmodel=medany \
    -fvisibility=hidden -nostdlib -nostartfiles \
    -I$(TARGET_DIR) \
    -T$(TARGET_DIR)/link.ld

.PHONY: all build sim gen compile run clean help

all: help

#
# Run the full riscv-dv flow for a specific test
# Usage: make run TEST=riscv_arithmetic_basic_test
#
run:
	@if [ -z "$(TEST)" ]; then \
		echo "ERROR: TEST not specified"; \
		echo "Usage: make run TEST=<test_name>"; \
		echo "Available tests:"; \
		echo "  - riscv_arithmetic_basic_test"; \
		echo "  - riscv_rand_instr_test"; \
		echo "  - riscv_jump_stress_test"; \
		echo "  - riscv_loop_test"; \
		echo "  - riscv_load_store_test"; \
		exit 1; \
	fi
	@mkdir -p $(OUT_DIR)/$(TEST)
	@echo "=== Generating test: $(TEST) ==="
	cd $(RISCV_DV_DIR) && $(PYTHON) run.py \
		--test $(TEST) \
		--target rv32i \
		--output $(OUT_DIR)/$(TEST) \
		--iterations $(ITERATIONS) \
		--steps gen \
		--simulator pyflow \
		--isa $(ISA) \
		--mabi $(ABI) \
		--sim_opts="--bare_program_mode=1"
	@echo "=== Compiling test ==="
	$(MAKE) compile_test TEST=$(TEST)
	@echo "=== Running on Spike ==="
	$(MAKE) spike_run TEST=$(TEST)
	@echo "=== Running on RTL ==="
	$(MAKE) rtl_run TEST=$(TEST)
	@echo "=== Comparing traces ==="
	$(MAKE) compare TEST=$(TEST)

#
# Compile a generated test
#
compile_test:
	@for asm in $(OUT_DIR)/$(TEST)/asm_test/*.S; do \
		base=$$(basename $$asm .S); \
		echo "Compiling $$base..."; \
		$(RISCV_GCC) $(GCC_FLAGS) -o $(OUT_DIR)/$(TEST)/$$base.elf $$asm; \
		$(RISCV_OBJCOPY) -O verilog $(OUT_DIR)/$(TEST)/$$base.elf $(OUT_DIR)/$(TEST)/$$base.byte.hex; \
		$(PYTHON) $(CURDIR)/scripts/hex_byte_to_word.py \
			$(OUT_DIR)/$(TEST)/$$base.byte.hex \
			$(OUT_DIR)/$(TEST)/$$base.hex; \
	done

#
# Run test on Spike
#
spike_run:
	@for elf in $(OUT_DIR)/$(TEST)/*.elf; do \
		base=$$(basename $$elf .elf); \
		echo "Running $$base on Spike..."; \
		$(SPIKE) --isa=$(ISA) -m0x10000:0x10000,0x80001000:0x1000 -l --log-commits $$elf 2>&1 | \
			head -10000 > $(OUT_DIR)/$(TEST)/$$base.spike.log || true; \
		cd $(RISCV_DV_DIR)/scripts && $(PYTHON) spike_log_to_trace_csv.py \
			--log $(OUT_DIR)/$(TEST)/$$base.spike.log \
			--csv $(OUT_DIR)/$(TEST)/$$base.spike.csv; \
	done

#
# Run test on RTL simulation
# Rebuilds with each hex file embedded via parameter
# Note: Skip .byte.hex files (intermediate format from objcopy)
#
rtl_run:
	@for elf in $(OUT_DIR)/$(TEST)/*.elf; do \
		base=$$(basename $$elf .elf); \
		hex=$(OUT_DIR)/$(TEST)/$$base.hex; \
		echo "Building RTL sim for $$base..."; \
		$(MAKE) -C $(RTL_SIM_DIR) clean build IMEM=$$hex; \
		echo "Running $$base on RTL..."; \
		$(BUILD_DIR)/svc_rv_sim \
			+trace=$(OUT_DIR)/$(TEST)/$$base.rtl.csv \
			+max_cycles=$(MAX_CYCLES); \
	done

#
# Compare Spike and RTL traces
#
compare:
	@for rtl_csv in $(OUT_DIR)/$(TEST)/*.rtl.csv; do \
		base=$$(basename $$rtl_csv .rtl.csv); \
		spike_csv=$(OUT_DIR)/$(TEST)/$$base.spike.csv; \
		if [ -f "$$spike_csv" ]; then \
			echo "Comparing $$base..."; \
			cd $(RISCV_DV_DIR)/scripts && $(PYTHON) instr_trace_compare.py \
				--csv_file_1 $$spike_csv \
				--csv_file_2 $$rtl_csv \
				--log $(OUT_DIR)/$(TEST)/$$base.compare.log; \
		else \
			echo "WARNING: Spike trace not found for $$base"; \
		fi \
	done

#
# Run all tests
#
run_all: build
	$(MAKE) run TEST=riscv_arithmetic_basic_test
	$(MAKE) run TEST=riscv_rand_instr_test
	$(MAKE) run TEST=riscv_jump_stress_test
	$(MAKE) run TEST=riscv_loop_test
	$(MAKE) run TEST=riscv_load_store_test

#
# Clean
#
clean:
	rm -rf $(OUT_DIR)
	$(MAKE) -C $(RTL_SIM_DIR) clean

#
# Help
#
help:
	@echo "SVC RISC-V riscv-dv Verification"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Python 3 with pyyaml"
	@echo "  - RISC-V GCC toolchain (riscv32-unknown-elf-gcc)"
	@echo "  - Spike RISC-V ISS"
	@echo "  - Verilator"
	@echo ""
	@echo "Targets:"
	@echo "  build     - Build Verilator RTL simulation"
	@echo "  run       - Run a single test (requires TEST=<name>)"
	@echo "  run_all   - Run all tests"
	@echo "  clean     - Clean build artifacts"
	@echo ""
	@echo "Available tests:"
	@echo "  - riscv_arithmetic_basic_test"
	@echo "  - riscv_rand_instr_test"
	@echo "  - riscv_jump_stress_test"
	@echo "  - riscv_loop_test"
	@echo "  - riscv_load_store_test"
	@echo ""
	@echo "Example:"
	@echo "  make build"
	@echo "  make run TEST=riscv_arithmetic_basic_test"
