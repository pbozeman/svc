ifndef RISCV_DV_MK
RISCV_DV_MK := 1

# riscv-dv integration for SVC RISC-V processor verification
#
# This provides targets for running Google's riscv-dv random
# instruction tests against the SVC processor.
#
# Prerequisites:
# - Python 3 with pyyaml
# - RISC-V GCC toolchain (riscv32-unknown-elf-gcc)
# - Spike RISC-V ISS
# - Verilator

RISCV_DV_DIR := $(SVC_DIR)/tb/riscv-dv

##############################################################################
#
# riscv-dv targets
#
##############################################################################

.PHONY: riscv-dv riscv-dv-build riscv-dv-clean

# Build the Verilator simulation
riscv-dv-build:
	$(MAKE) -C $(RISCV_DV_DIR) build

# Run a specific riscv-dv test
# Usage: make riscv-dv TEST=riscv_arithmetic_basic_test
riscv-dv: riscv-dv-build
	$(MAKE) -C $(RISCV_DV_DIR) run TEST=$(TEST)

# Run all riscv-dv tests
riscv-dv-all: riscv-dv-build
	$(MAKE) -C $(RISCV_DV_DIR) run_all

# Clean riscv-dv build artifacts
riscv-dv-clean:
	$(MAKE) -C $(RISCV_DV_DIR) clean

# Help for riscv-dv
riscv-dv-help:
	$(MAKE) -C $(RISCV_DV_DIR) help

endif
