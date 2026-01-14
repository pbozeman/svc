ifndef SIM_MK
SIM_MK := 1

include mk/dirs.mk
include mk/format.mk
include mk/iverilog.mk

# Verilator simulation command
VERILATOR_SIM_FLAGS := --cc --exe --build --timing
VERILATOR_SIM_FLAGS += -Wall -Wno-PINCONNECTEMPTY -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM
VERILATOR_SIM_FLAGS += -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND
VERILATOR_SIM_FLAGS += -O3
VERILATOR_SIM_FLAGS += $(I_RTL) $(I_EXT) -I$(PRJ_TB_DIR)
VERILATOR_SIM_FLAGS += -LDFLAGS -lutil
VERILATOR_SIM_FLAGS += -CFLAGS '-Wall -Werror'
VERILATOR_SIM := verilator $(VERILATOR_SIM_FLAGS)

# Standalone simulation sources and modules
# Only find *_sim.sv files in subdirectories (not top-level rtl/)
# to exclude infrastructure like svc_soc_sim.sv
SIM_SV := $(shell find $(PRJ_RTL_DIR)/*/ -name '*_sim.sv' 2>/dev/null)
SIM_MODULES := $(basename $(notdir $(SIM_SV)))
SIM_SUBDIRS := $(shell find $(PRJ_RTL_DIR) -type d 2>/dev/null)

# Tell Make where to find _sim.sv files
vpath %_sim.sv $(SIM_SUBDIRS)

# Sim output directories
SIM_BUILD_DIR := $(BUILD_DIR)/sim
SIM_IV_BUILD_DIR := $(BUILD_DIR)/sim_iv

# C++ wrapper for Verilator sims
SIM_MAIN_CPP := $(SVC_DIR)/tb/cpp/sim_main.cpp

##############################################################################
#
# RISC-V Architecture-Specific Simulations
#
# NOTE: This section is cross-coupled to sw/Makefile.common which defines
# the architecture variants (rv32i, rv32im, rv32i_zmmul) and their build
# paths. These should ideally be unified into a higher-level project
# configuration to avoid drift.
#
##############################################################################

# Auto-detect RV simulation modules (rv_*_sim pattern)
RV_SIM_MODULES := $(patsubst rv_%_sim,%,$(filter rv_%_sim,$(SIM_MODULES)))

ifneq ($(RV_SIM_MODULES),)

# Base RV simulation targets (rv_*_sim without arch suffix) default to rv32i
# This creates a complete rule with hex dependency and Verilator build recipe
# (prerequisite-only rules don't merge correctly with pattern rules in Make)
define rv_base_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_sim/Vrv_$(1)_sim: $(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_sim.d
	@$$(VERILATOR_SIM) \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex"' \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_base_sim_rule,$(mod))))

# Include generated dependency files for software
# These .d files add source dependencies (e.g., main.c, crt0.S) to hex targets
-include $(wildcard $(BUILD_DIR)/sw/*/*/*.hex.d)

# Architecture-specific simulation pattern rules
# Pattern: rv_<module>_<arch>_sim depends on corresponding hex file
$(SIM_BUILD_DIR)/rv_%_i_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_im_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_i_zmmul_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# SRAM pipelined simulation pattern rules
$(SIM_BUILD_DIR)/rv_%_sram_i_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_sram_im_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_sram_i_zmmul_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# SRAM single-cycle simulation pattern rules
$(SIM_BUILD_DIR)/rv_%_sram_sc_i_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_sram_sc_im_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_sram_sc_i_zmmul_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# BRAM cache simulation pattern rules
$(SIM_BUILD_DIR)/rv_%_cache_i_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_cache_im_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_cache_i_zmmul_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# PC_REG-enabled simulation pattern rules
$(SIM_BUILD_DIR)/rv_%_i_reg_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_im_reg_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_i_zmmul_reg_sim/Vrv_%_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# Verilator build rule for architecture-specific simulations
# Generate rules for each RV module and architecture combination
define rv_arch_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim.d
	@$$(VERILATOR_SIM) \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_$(2)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Verilator build rule for PC_REG-enabled architecture-specific simulations
define rv_arch_reg_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_PC_REG \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_$(2)_reg_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_$(2)_reg_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate PC_REG-enabled rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# SRAM pipelined simulation build rules
define rv_sram_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_MEM_SRAM \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_sram_$(2)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_sram_$(2)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate SRAM pipelined rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# SRAM single-cycle simulation build rules
define rv_sram_sc_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_MEM_SRAM \
		-DSVC_CPU_SINGLE_CYCLE \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_sram_sc_$(2)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate SRAM single-cycle rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# BRAM cache simulation build rules
define rv_cache_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_MEM_BRAM_CACHE \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_cache_$(2)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate BRAM cache rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# BRAM cache + PC_REG simulation build rules
define rv_cache_reg_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_MEM_BRAM_CACHE \
		-DSVC_PC_REG \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_cache_$(2)_reg_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate BRAM cache + PC_REG rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# BRAM cache with latency injection simulation build rules
# Uses svc_axi_mem_latency for DDR3/MIG-like timing stress testing
define rv_cache_latency_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim/Vrv_$(1)_sim
$(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim/Vrv_$(1)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim.dep -o /dev/null \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) $$(word 2,$$^) 2>/dev/null || true
	@echo "$$@: $$$$(tr '\n' ' ' < $(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim.dep)" > $(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim.d
	@$$(VERILATOR_SIM) \
		-DSVC_MEM_BRAM_CACHE \
		-DSVC_AXI_LATENCY \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		-I$$(PRJ_RTL_DIR)/rv_$(1) \
		--Mdir $(SIM_BUILD_DIR)/rv_$(1)_cache_latency_$(2)_sim \
		--top-module rv_$(1)_sim \
		-CFLAGS '-DSIM_HEADER=\"Vrv_$(1)_sim.h\" -DSIM_TOP=Vrv_$(1)_sim -DSIM_NAME=\"rv_$(1)_cache_latency_$(2)_sim\"' \
		$$(word 2,$$^) $(SIM_MAIN_CPP)
endef

# Generate BRAM cache latency rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_latency_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_latency_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_latency_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Phony targets for convenience
# Base RV sims (rv_*_sim without arch suffix) - defaults to rv32i
RV_BASE_SIMS := $(addprefix rv_,$(addsuffix _sim,$(RV_SIM_MODULES)))
RV_I_SIMS := $(addprefix rv_,$(addsuffix _i_sim,$(RV_SIM_MODULES)))
RV_IM_SIMS := $(addprefix rv_,$(addsuffix _im_sim,$(RV_SIM_MODULES)))
RV_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _i_zmmul_sim,$(RV_SIM_MODULES)))

# SRAM pipelined phony targets
RV_SRAM_I_SIMS := $(addprefix rv_,$(addsuffix _sram_i_sim,$(RV_SIM_MODULES)))
RV_SRAM_IM_SIMS := $(addprefix rv_,$(addsuffix _sram_im_sim,$(RV_SIM_MODULES)))
RV_SRAM_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _sram_i_zmmul_sim,$(RV_SIM_MODULES)))

# SRAM single-cycle phony targets
RV_SRAM_SC_I_SIMS := $(addprefix rv_,$(addsuffix _sram_sc_i_sim,$(RV_SIM_MODULES)))
RV_SRAM_SC_IM_SIMS := $(addprefix rv_,$(addsuffix _sram_sc_im_sim,$(RV_SIM_MODULES)))
RV_SRAM_SC_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _sram_sc_i_zmmul_sim,$(RV_SIM_MODULES)))

# BRAM cache phony targets
RV_CACHE_I_SIMS := $(addprefix rv_,$(addsuffix _cache_i_sim,$(RV_SIM_MODULES)))
RV_CACHE_IM_SIMS := $(addprefix rv_,$(addsuffix _cache_im_sim,$(RV_SIM_MODULES)))
RV_CACHE_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _cache_i_zmmul_sim,$(RV_SIM_MODULES)))

# BRAM cache + PC_REG phony targets
RV_CACHE_REG_I_SIMS := $(addprefix rv_,$(addsuffix _cache_i_reg_sim,$(RV_SIM_MODULES)))
RV_CACHE_REG_IM_SIMS := $(addprefix rv_,$(addsuffix _cache_im_reg_sim,$(RV_SIM_MODULES)))
RV_CACHE_REG_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _cache_i_zmmul_reg_sim,$(RV_SIM_MODULES)))

# PC_REG-enabled phony targets
RV_I_REG_SIMS := $(addprefix rv_,$(addsuffix _i_reg_sim,$(RV_SIM_MODULES)))
RV_IM_REG_SIMS := $(addprefix rv_,$(addsuffix _im_reg_sim,$(RV_SIM_MODULES)))
RV_I_ZMMUL_REG_SIMS := $(addprefix rv_,$(addsuffix _i_zmmul_reg_sim,$(RV_SIM_MODULES)))

# BRAM cache with latency injection phony targets
RV_CACHE_LATENCY_I_SIMS := $(addprefix rv_,$(addsuffix _cache_latency_i_sim,$(RV_SIM_MODULES)))
RV_CACHE_LATENCY_IM_SIMS := $(addprefix rv_,$(addsuffix _cache_latency_im_sim,$(RV_SIM_MODULES)))
RV_CACHE_LATENCY_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _cache_latency_i_zmmul_sim,$(RV_SIM_MODULES)))

# Debug flags passed as plusargs to the simulation
SIM_DBG_FLAGS := \
	$(if $(SVC_RV_DBG_CPU),+SVC_RV_DBG_CPU=$(SVC_RV_DBG_CPU)) \
	$(if $(SVC_RV_DBG_IF),+SVC_RV_DBG_IF=$(SVC_RV_DBG_IF)) \
	$(if $(SVC_RV_DBG_ID),+SVC_RV_DBG_ID=$(SVC_RV_DBG_ID)) \
	$(if $(SVC_RV_DBG_EX),+SVC_RV_DBG_EX=$(SVC_RV_DBG_EX)) \
	$(if $(SVC_RV_DBG_MEM),+SVC_RV_DBG_MEM=$(SVC_RV_DBG_MEM)) \
	$(if $(SVC_RV_DBG_WB),+SVC_RV_DBG_WB=$(SVC_RV_DBG_WB)) \
	$(if $(SVC_RV_DBG_HAZ),+SVC_RV_DBG_HAZ=$(SVC_RV_DBG_HAZ)) \
	$(if $(SVC_SIM_PREFIX),+SVC_SIM_PREFIX=$(SVC_SIM_PREFIX))

.PHONY: $(RV_BASE_SIMS) $(RV_I_SIMS) $(RV_IM_SIMS) $(RV_I_ZMMUL_SIMS) $(RV_SRAM_I_SIMS) $(RV_SRAM_IM_SIMS) $(RV_SRAM_I_ZMMUL_SIMS) $(RV_SRAM_SC_I_SIMS) $(RV_SRAM_SC_IM_SIMS) $(RV_SRAM_SC_I_ZMMUL_SIMS) $(RV_CACHE_I_SIMS) $(RV_CACHE_IM_SIMS) $(RV_CACHE_I_ZMMUL_SIMS) $(RV_CACHE_REG_I_SIMS) $(RV_CACHE_REG_IM_SIMS) $(RV_CACHE_REG_I_ZMMUL_SIMS) $(RV_I_REG_SIMS) $(RV_IM_REG_SIMS) $(RV_I_ZMMUL_REG_SIMS) $(RV_CACHE_LATENCY_I_SIMS) $(RV_CACHE_LATENCY_IM_SIMS) $(RV_CACHE_LATENCY_I_ZMMUL_SIMS)

# Execution targets - run the Verilator binary
# Use explicit path construction because GNU make has issues with multiple % in prerequisites

# Base RV sims (rv_*_sim) - defaults to rv32i
# Note: $($*_SIM_FLAGS) allows per-module flags like echo_SIM_FLAGS
# When UART_STDIN is in flags and stdin is a tty, use raw mode for proper terminal I/O
$(RV_BASE_SIMS): rv_%_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sim/Vrv_$*_sim
	@if echo "$($*_SIM_FLAGS)" | grep -q UART_STDIN && [ -t 0 ]; then \
		old_stty=$$(stty -g); \
		stty -icanon -echo; \
		$(SIM_BUILD_DIR)/rv_$*_sim/Vrv_$*_sim $(SIM_DBG_FLAGS) $($*_SIM_FLAGS); \
		stty $$old_stty; \
	else \
		$(SIM_BUILD_DIR)/rv_$*_sim/Vrv_$*_sim $(SIM_DBG_FLAGS) $($*_SIM_FLAGS); \
	fi

# Helper for running sim with optional raw terminal mode for UART_STDIN
# Usage: $(call run_sim,binary_path,module_name)
# When UART_STDIN is in flags and stdin is a tty, use raw mode for proper terminal I/O
# Use -icanon -echo to disable line buffering and local echo while keeping output processing
define run_sim
@if echo "$($(2)_SIM_FLAGS)" | grep -q UART_STDIN && [ -t 0 ]; then \
	old_stty=$$(stty -g); \
	stty -icanon -echo; \
	$(1) $(SIM_DBG_FLAGS) $($(2)_SIM_FLAGS); \
	stty $$old_stty; \
else \
	$(1) $(SIM_DBG_FLAGS) $($(2)_SIM_FLAGS); \
fi
endef

$(RV_I_SIMS): rv_%_i_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_i_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_i_sim/Vrv_$*_sim,$*)

$(RV_IM_SIMS): rv_%_im_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_im_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_im_sim/Vrv_$*_sim,$*)

$(RV_I_ZMMUL_SIMS): rv_%_i_zmmul_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_i_zmmul_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_i_zmmul_sim/Vrv_$*_sim,$*)

# PC_REG-enabled execution targets
$(RV_I_REG_SIMS): rv_%_i_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_i_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_i_reg_sim/Vrv_$*_sim,$*)

$(RV_IM_REG_SIMS): rv_%_im_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_im_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_im_reg_sim/Vrv_$*_sim,$*)

$(RV_I_ZMMUL_REG_SIMS): rv_%_i_zmmul_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_i_zmmul_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_i_zmmul_reg_sim/Vrv_$*_sim,$*)

# Convenience alias: CoreMark requires hardware multiply, so default to RV32IM.
.PHONY: rv_coremark_reg_sim
rv_coremark_reg_sim: rv_coremark_im_reg_sim

# Convenience alias: CoreMark cache + PC_REG (defaults to RV32IM).
.PHONY: rv_coremark_cache_reg_sim
rv_coremark_cache_reg_sim: rv_coremark_cache_im_reg_sim

# SRAM pipelined execution targets
$(RV_SRAM_I_SIMS): rv_%_sram_i_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_i_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_i_sim/Vrv_$*_sim,$*)

$(RV_SRAM_IM_SIMS): rv_%_sram_im_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_im_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_im_sim/Vrv_$*_sim,$*)

$(RV_SRAM_I_ZMMUL_SIMS): rv_%_sram_i_zmmul_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_i_zmmul_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_i_zmmul_sim/Vrv_$*_sim,$*)

# SRAM single-cycle execution targets
$(RV_SRAM_SC_I_SIMS): rv_%_sram_sc_i_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_sc_i_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_sc_i_sim/Vrv_$*_sim,$*)

$(RV_SRAM_SC_IM_SIMS): rv_%_sram_sc_im_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_sc_im_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_sc_im_sim/Vrv_$*_sim,$*)

$(RV_SRAM_SC_I_ZMMUL_SIMS): rv_%_sram_sc_i_zmmul_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_sram_sc_i_zmmul_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_sram_sc_i_zmmul_sim/Vrv_$*_sim,$*)

# BRAM cache execution targets
$(RV_CACHE_I_SIMS): rv_%_cache_i_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_i_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_i_sim/Vrv_$*_sim,$*)

$(RV_CACHE_IM_SIMS): rv_%_cache_im_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_im_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_im_sim/Vrv_$*_sim,$*)

$(RV_CACHE_I_ZMMUL_SIMS): rv_%_cache_i_zmmul_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_i_zmmul_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_i_zmmul_sim/Vrv_$*_sim,$*)

# BRAM cache + PC_REG execution targets
$(RV_CACHE_REG_I_SIMS): rv_%_cache_i_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_i_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_i_reg_sim/Vrv_$*_sim,$*)

$(RV_CACHE_REG_IM_SIMS): rv_%_cache_im_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_im_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_im_reg_sim/Vrv_$*_sim,$*)

$(RV_CACHE_REG_I_ZMMUL_SIMS): rv_%_cache_i_zmmul_reg_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_i_zmmul_reg_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_i_zmmul_reg_sim/Vrv_$*_sim,$*)

# BRAM cache with latency injection execution targets
$(RV_CACHE_LATENCY_I_SIMS): rv_%_cache_latency_i_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_latency_i_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_latency_i_sim/Vrv_$*_sim,$*)

$(RV_CACHE_LATENCY_IM_SIMS): rv_%_cache_latency_im_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_latency_im_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_latency_im_sim/Vrv_$*_sim,$*)

$(RV_CACHE_LATENCY_I_ZMMUL_SIMS): rv_%_cache_latency_i_zmmul_sim:
	@$(MAKE) $(SIM_BUILD_DIR)/rv_$*_cache_latency_i_zmmul_sim/Vrv_$*_sim
	$(call run_sim,$(SIM_BUILD_DIR)/rv_$*_cache_latency_i_zmmul_sim/Vrv_$*_sim,$*)

# Hex files are built by targeted sw builds (recursive make into sw/<module>)
# The .d files (included above) provide source dependencies for rebuild detection
# Build only the specific program/arch needed rather than all software
# Pass SVC_SIM=1 to enable simulation-specific settings (e.g., fewer iterations)
# Pass SVC_DISABLE_MMIO if set (deterministic I/O stubs)
SW_BUILD_FLAGS := SVC_SIM=1 $(if $(SVC_DISABLE_MMIO),SVC_DISABLE_MMIO=1)

define rv_hex_rules
$(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i $(SW_BUILD_FLAGS)

$(BUILD_DIR)/sw/rv32im/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32im $(SW_BUILD_FLAGS)

$(BUILD_DIR)/sw/rv32i_zmmul/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i_zmmul $(SW_BUILD_FLAGS)

$(BUILD_DIR)/sw/rv32i/$(1)/$(1)_128.hex: $(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i ../../.build/sw/rv32i/$(1)/$(1)_128.hex

$(BUILD_DIR)/sw/rv32im/$(1)/$(1)_128.hex: $(BUILD_DIR)/sw/rv32im/$(1)/$(1).hex
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32im ../../.build/sw/rv32im/$(1)/$(1)_128.hex

$(BUILD_DIR)/sw/rv32i_zmmul/$(1)/$(1)_128.hex: $(BUILD_DIR)/sw/rv32i_zmmul/$(1)/$(1).hex
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i_zmmul ../../.build/sw/rv32i_zmmul/$(1)/$(1)_128.hex
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_hex_rules,$(mod))))

##############################################################################
#
# Icarus Verilog Simulations (*_simi targets)
#
# These provide debug output support via $value$plusargs which Verilator
# doesn't support. Use these when you need SVC_RV_DBG_CPU=1 etc.
#
##############################################################################

# Icarus phony targets (append 'i' to sim targets)
RV_I_SIMIS := $(addprefix rv_,$(addsuffix _i_simi,$(RV_SIM_MODULES)))
RV_IM_SIMIS := $(addprefix rv_,$(addsuffix _im_simi,$(RV_SIM_MODULES)))
RV_I_ZMMUL_SIMIS := $(addprefix rv_,$(addsuffix _i_zmmul_simi,$(RV_SIM_MODULES)))
RV_I_REG_SIMIS := $(addprefix rv_,$(addsuffix _i_reg_simi,$(RV_SIM_MODULES)))
RV_IM_REG_SIMIS := $(addprefix rv_,$(addsuffix _im_reg_simi,$(RV_SIM_MODULES)))
RV_I_ZMMUL_REG_SIMIS := $(addprefix rv_,$(addsuffix _i_zmmul_reg_simi,$(RV_SIM_MODULES)))
RV_SRAM_I_SIMIS := $(addprefix rv_,$(addsuffix _sram_i_simi,$(RV_SIM_MODULES)))
RV_SRAM_IM_SIMIS := $(addprefix rv_,$(addsuffix _sram_im_simi,$(RV_SIM_MODULES)))
RV_SRAM_I_ZMMUL_SIMIS := $(addprefix rv_,$(addsuffix _sram_i_zmmul_simi,$(RV_SIM_MODULES)))
RV_SRAM_SC_I_SIMIS := $(addprefix rv_,$(addsuffix _sram_sc_i_simi,$(RV_SIM_MODULES)))
RV_SRAM_SC_IM_SIMIS := $(addprefix rv_,$(addsuffix _sram_sc_im_simi,$(RV_SIM_MODULES)))
RV_SRAM_SC_I_ZMMUL_SIMIS := $(addprefix rv_,$(addsuffix _sram_sc_i_zmmul_simi,$(RV_SIM_MODULES)))
RV_CACHE_I_SIMIS := $(addprefix rv_,$(addsuffix _cache_i_simi,$(RV_SIM_MODULES)))
RV_CACHE_IM_SIMIS := $(addprefix rv_,$(addsuffix _cache_im_simi,$(RV_SIM_MODULES)))
RV_CACHE_I_ZMMUL_SIMIS := $(addprefix rv_,$(addsuffix _cache_i_zmmul_simi,$(RV_SIM_MODULES)))
RV_CACHE_I_REG_SIMIS := $(addprefix rv_,$(addsuffix _cache_i_reg_simi,$(RV_SIM_MODULES)))
RV_CACHE_IM_REG_SIMIS := $(addprefix rv_,$(addsuffix _cache_im_reg_simi,$(RV_SIM_MODULES)))
RV_CACHE_I_ZMMUL_REG_SIMIS := $(addprefix rv_,$(addsuffix _cache_i_zmmul_reg_simi,$(RV_SIM_MODULES)))

# Base RV simi targets (rv_*_simi without arch suffix) default to rv32i
RV_BASE_SIMIS := $(addprefix rv_,$(addsuffix _simi,$(RV_SIM_MODULES)))

.PHONY: $(RV_BASE_SIMIS) $(RV_I_SIMIS) $(RV_IM_SIMIS) $(RV_I_ZMMUL_SIMIS) $(RV_I_REG_SIMIS) $(RV_IM_REG_SIMIS) $(RV_I_ZMMUL_REG_SIMIS) $(RV_SRAM_I_SIMIS) $(RV_SRAM_IM_SIMIS) $(RV_SRAM_I_ZMMUL_SIMIS) $(RV_SRAM_SC_I_SIMIS) $(RV_SRAM_SC_IM_SIMIS) $(RV_SRAM_SC_I_ZMMUL_SIMIS) $(RV_CACHE_I_SIMIS) $(RV_CACHE_IM_SIMIS) $(RV_CACHE_I_ZMMUL_SIMIS) $(RV_CACHE_I_REG_SIMIS) $(RV_CACHE_IM_REG_SIMIS) $(RV_CACHE_I_ZMMUL_REG_SIMIS)

# Icarus build rule for base RV simulations (rv_*_simi -> rv32i)
define rv_base_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_simi: $(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex"' \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_base_simi_rule,$(mod))))

# Icarus build rule for architecture-specific simulations
define rv_arch_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_$(2)_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_$(2)_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus build rule for PC_REG-enabled architecture-specific simulations
define rv_arch_reg_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_$(2)_reg_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_$(2)_reg_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DSVC_PC_REG \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_reg_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus SRAM pipelined simulation build rules
define rv_sram_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_sram_$(2)_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_sram_$(2)_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DSVC_MEM_SRAM \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus SRAM single-cycle simulation build rules
define rv_sram_sc_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_sram_sc_$(2)_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DSVC_MEM_SRAM \
		-DSVC_CPU_SINGLE_CYCLE \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_sram_sc_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus BRAM cache simulation build rules
define rv_cache_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_cache_$(2)_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_cache_$(2)_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DSVC_MEM_BRAM_CACHE \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus BRAM cache + PC_REG simulation build rules
define rv_cache_reg_simi_rule
.PRECIOUS: $(SIM_IV_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_simi
$(SIM_IV_BUILD_DIR)/rv_$(1)_cache_$(2)_reg_simi: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep \
		-DSVC_MEM_BRAM_CACHE \
		-DSVC_PC_REG \
		-DRV_IMEM_DEPTH=$$(or $$($(1)_RV_IMEM_DEPTH),$$(RV_IMEM_DEPTH)) \
		-DRV_DMEM_DEPTH=$$(or $$($(1)_RV_DMEM_DEPTH),$$(RV_DMEM_DEPTH)) \
		-DRV_SIM_HEX='"$(3)/$(1)/$(1).hex"' \
		$(if $(filter i_zmmul,$(2)),-DRV_ARCH_ZMMUL) \
		$(if $(filter im,$(2)),-DRV_ARCH_M) \
		$$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_simi_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_simi_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_cache_reg_simi_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Icarus execution targets - run with VVP
$(RV_BASE_SIMIS): rv_%_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_I_SIMIS): rv_%_i_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_i_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_i_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_IM_SIMIS): rv_%_im_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_im_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_im_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_I_REG_SIMIS): rv_%_i_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_i_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_i_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_IM_REG_SIMIS): rv_%_im_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_im_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_im_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_I_ZMMUL_REG_SIMIS): rv_%_i_zmmul_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_i_zmmul_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_i_zmmul_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_I_ZMMUL_SIMIS): rv_%_i_zmmul_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_i_zmmul_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_i_zmmul_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_I_SIMIS): rv_%_sram_i_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_i_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_i_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_IM_SIMIS): rv_%_sram_im_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_im_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_im_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_I_ZMMUL_SIMIS): rv_%_sram_i_zmmul_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_i_zmmul_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_i_zmmul_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_SC_I_SIMIS): rv_%_sram_sc_i_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_i_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_i_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_SC_IM_SIMIS): rv_%_sram_sc_im_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_im_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_im_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_SRAM_SC_I_ZMMUL_SIMIS): rv_%_sram_sc_i_zmmul_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_i_zmmul_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_sram_sc_i_zmmul_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_I_SIMIS): rv_%_cache_i_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_IM_SIMIS): rv_%_cache_im_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_im_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_im_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_I_REG_SIMIS): rv_%_cache_i_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_IM_REG_SIMIS): rv_%_cache_im_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_im_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_im_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_I_ZMMUL_REG_SIMIS): rv_%_cache_i_zmmul_reg_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_zmmul_reg_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_zmmul_reg_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

$(RV_CACHE_I_ZMMUL_SIMIS): rv_%_cache_i_zmmul_simi:
	@$(MAKE) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_zmmul_simi
	@$(VVP) $(SIM_IV_BUILD_DIR)/rv_$*_cache_i_zmmul_simi $(SIM_DBG_FLAGS) $($*_SIM_FLAGS)

# Convenience alias: CoreMark requires hardware multiply, so default to RV32IM.
.PHONY: rv_coremark_reg_simi
rv_coremark_reg_simi: rv_coremark_im_reg_simi

endif # RV_SIM_MODULES

##############################################################################
#
# Sim Formatting
#
##############################################################################
format: format_sim

.PHONY: format_sim
format_sim:
	@$(FORMATTER) $(SIM_SV)

##############################################################################
#
# Sim Linting
#
##############################################################################
.PHONY: lint_sim
lint: lint_sim

define lint_sim_rule
lint_sim: lint_$(1)
lint_$(1):
	@$$(LINTER) $(I_RTL) -I$(PRJ_TB_DIR) -I$(PRJ_RTL_DIR)/$(patsubst %_sim,%, $(notdir $1)) $(1).sv
endef

$(foreach sim, $(SIM_MODULES), $(eval $(call lint_sim_rule,$(sim))))

##############################################################################
#
# Sim Compilation and Execution
#
##############################################################################

# Pattern rule to build and run a standalone sim
# Note: RV base sims (rv_*_sim) are handled separately above with explicit rules
SIM_MODULES_NON_RV_BASE := $(filter-out $(RV_BASE_SIMS),$(SIM_MODULES))
.PHONY: $(SIM_MODULES_NON_RV_BASE)
$(SIM_MODULES_NON_RV_BASE): %: $(SIM_BUILD_DIR)/%/V%
	@$(SIM_BUILD_DIR)/$*/V$* $(SIM_DBG_FLAGS)

# Determine the source subdirectory for each sim
SIM_PRJ_INC = $(PRJ_RTL_DIR)/$(patsubst %_sim,%, $(notdir $(*)))

# Pattern rule to compile a sim with Verilator
.PRECIOUS: $(SIM_BUILD_DIR)/%/V%
$(SIM_BUILD_DIR)/%/V%: %.sv $(SIM_MAIN_CPP) Makefile | $(SIM_BUILD_DIR)
	@$(IVERILOG) -M $(SIM_BUILD_DIR)/$(notdir $*).dep -o /dev/null \
		$(I_RTL) -I$(PRJ_TB_DIR) -I$(SIM_PRJ_INC) $< 2>/dev/null || true
	@echo "$@: $$(tr '\n' ' ' < $(SIM_BUILD_DIR)/$(notdir $*).dep)" > $(SIM_BUILD_DIR)/$(notdir $*).d
	@$(VERILATOR_SIM) \
		$(if $(filter rv_%,$(notdir $*)),\
			-DRV_IMEM_DEPTH=$(or $($(patsubst rv_%_sim,%,$(notdir $*))_RV_IMEM_DEPTH),$(RV_IMEM_DEPTH)) \
			-DRV_DMEM_DEPTH=$(or $($(patsubst rv_%_sim,%,$(notdir $*))_RV_DMEM_DEPTH),$(RV_DMEM_DEPTH)) \
			-DRV_SIM_HEX='"$(BUILD_DIR)/sw/rv32i/$(patsubst rv_%_sim,%,$(notdir $*))/$(patsubst rv_%_sim,%,$(notdir $*)).hex"') \
		-I$(SIM_PRJ_INC) \
		--Mdir $(SIM_BUILD_DIR)/$(notdir $*) \
		--top-module $(notdir $*) \
		-CFLAGS '-DSIM_HEADER=\"V$(notdir $*).h\" -DSIM_TOP=V$(notdir $*) -DSIM_NAME=\"$(notdir $*)\"' \
		$< $(SIM_MAIN_CPP)

##############################################################################
#
# Generic Icarus Verilog Simulations (*_simi targets)
#
##############################################################################

# Generate *_simi module names from *_sim modules (excluding RV modules which have specific rules)
SIM_MODULES_NON_RV := $(filter-out rv_%,$(SIM_MODULES))
SIM_MODULES_I := $(addsuffix i,$(SIM_MODULES_NON_RV))

# Pattern rule to build and run a standalone sim with Icarus
.PHONY: $(SIM_MODULES_I)
$(SIM_MODULES_I): %i: $(SIM_IV_BUILD_DIR)/%i
	@$(VVP) $(SIM_IV_BUILD_DIR)/$*i $(SIM_DBG_FLAGS)

# Determine the source subdirectory for each simi
# Pattern %i means $* already has trailing 'i' stripped (e.g., uart_demo_sim)
SIMI_PRJ_INC = $(PRJ_RTL_DIR)/$(patsubst %_sim,%, $(notdir $(*)))

# Pattern rule to compile a sim with Icarus Verilog
# Target ends in 'i' (e.g., uart_demo_simi), source is without 'i' (uart_demo_sim.sv)
.PRECIOUS: $(SIM_IV_BUILD_DIR)/%i
$(SIM_IV_BUILD_DIR)/%i: %.sv Makefile | $(SIM_IV_BUILD_DIR)
	@$(IVERILOG) -M $(@).dep \
		$(if $(filter rv_%,$(notdir $*)),\
			-DRV_IMEM_DEPTH=$(or $($(patsubst rv_%_sim,%,$(notdir $*))_RV_IMEM_DEPTH),$(RV_IMEM_DEPTH)) \
			-DRV_DMEM_DEPTH=$(or $($(patsubst rv_%_sim,%,$(notdir $*))_RV_DMEM_DEPTH),$(RV_DMEM_DEPTH)) \
			-DRV_SIM_HEX='"$(BUILD_DIR)/sw/rv32i/$(patsubst rv_%_sim,%,$(notdir $*))/$(patsubst rv_%_sim,%,$(notdir $*)).hex"') \
		$(I_RTL) -I$(PRJ_TB_DIR) -I$(SIMI_PRJ_INC) -o $@ $< 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $${PIPESTATUS[0]}
	@echo "$@: $$(tr '\n' ' ' < $(@).dep)" > $(@).d

##############################################################################
#
# Build Maintenance
#
##############################################################################
$(SIM_BUILD_DIR):
	@mkdir -p $(@)

$(SIM_IV_BUILD_DIR):
	@mkdir -p $(@)

.PHONY: clean_sim
clean_sim:
	@rm -rf $(SIM_BUILD_DIR) $(SIM_IV_BUILD_DIR)

clean: clean_sim

##############################################################################
#
# Run all simulations
#
##############################################################################
.PHONY: sim
sim:
	@$(MAKE) $(SIM_MODULES) SVC_SIM_PREFIX=1

##############################################################################
#
# Help
#
##############################################################################
.PHONY: list_sim
list_sim:
	@echo "Available sim targets (Verilator):"; \
	$(foreach t,$(SIM_MODULES),echo "  $t";) \
	echo ""; \
	echo "Available simi targets (Icarus, debug support):"; \
	$(foreach t,$(SIM_MODULES),echo "  $ti";) \
	echo

endif
