# SVC RISC-V riscv-dv Verilator simulation Makefile

# Directories
TOP_DIR := $(shell cd ../../.. && pwd)
RTL_DIR := $(TOP_DIR)/rtl
TB_DIR := $(TOP_DIR)/tb
BUILD_DIR := $(TOP_DIR)/.build/riscv-dv

# RTL include paths
RTL_SUBDIRS := $(shell find $(RTL_DIR) -type d)
I_RTL := $(foreach d, $(RTL_SUBDIRS), -I$(d))

# Source files
TB_SV := svc_rv_riscv_dv_tb.sv
TB_CPP := svc_rv_riscv_dv_tb.cpp

# Verilator settings
VERILATOR := verilator
VERILATOR_FLAGS := --cc --exe --build \
    -Wall -Wno-fatal \
    --trace \
    -DRISCV_FORMAL \
    $(I_RTL) \
    -I. \
    --Mdir $(BUILD_DIR) \
    -o $(BUILD_DIR)/svc_rv_sim

.PHONY: all build clean run

all: build

# Build with hex file embedded via parameter
# Usage: make build IMEM=/path/to/program.hex
build:
	@mkdir -p $(BUILD_DIR)
	$(VERILATOR) $(VERILATOR_FLAGS) \
		-GIMEM_INIT=\"$(IMEM)\" \
		$(TB_SV) $(TB_CPP)

clean:
	rm -rf $(BUILD_DIR)

# Run simulation
# Usage: make run TRACE=/path/to/trace.csv
run:
	$(BUILD_DIR)/svc_rv_sim +trace=$(TRACE) +max_cycles=$(MAX_CYCLES)

# Help
help:
	@echo "SVC RISC-V riscv-dv Verilator Simulation"
	@echo ""
	@echo "Targets:"
	@echo "  build       - Build Verilator simulation (requires IMEM=path/to/file.hex)"
	@echo "  run         - Run simulation (requires TRACE=path/to/trace.csv)"
	@echo "  clean       - Clean build artifacts"
	@echo ""
	@echo "Example:"
	@echo "  make build IMEM=test.hex"
	@echo "  make run TRACE=trace.csv MAX_CYCLES=1000000"
