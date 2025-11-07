ifndef SIM_MK
SIM_MK := 1

include mk/dirs.mk
include mk/format.mk

# Standalone simulation sources and modules
# Only find *_sim.sv files in subdirectories (not top-level rtl/)
# to exclude infrastructure like svc_soc_sim.sv
SIM_SV := $(shell find $(PRJ_RTL_DIR)/*/ -name '*_sim.sv' 2>/dev/null)
SIM_MODULES := $(basename $(notdir $(SIM_SV)))
SIM_SUBDIRS := $(shell find $(PRJ_RTL_DIR) -type d 2>/dev/null)

# Tell Make where to find _sim.sv files
vpath %_sim.sv $(SIM_SUBDIRS)

# Sim output directory
SIM_BUILD_DIR := $(BUILD_DIR)/sim

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
# This adds hex file dependency to the generic compilation rule
define rv_base_sim_dep
$(SIM_BUILD_DIR)/rv_$(1)_sim: $(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_base_sim_dep,$(mod))))

# Include generated dependency files for software
# These .d files add source dependencies (e.g., main.c, crt0.S) to hex targets
-include $(wildcard $(BUILD_DIR)/sw/*/*/*.hex.d)

# Architecture-specific simulation pattern rules
# Pattern: rv_<module>_<arch>_sim depends on corresponding hex file
# Examples: rv_hello_i_sim, rv_hello_im_sim, rv_hello_i_zmmul_sim
$(SIM_BUILD_DIR)/rv_%_i_sim: $(BUILD_DIR)/sw/rv32i/%/%.hex
$(SIM_BUILD_DIR)/rv_%_im_sim: $(BUILD_DIR)/sw/rv32im/%/%.hex
$(SIM_BUILD_DIR)/rv_%_i_zmmul_sim: $(BUILD_DIR)/sw/rv32i_zmmul/%/%.hex

# Architecture-specific simulation build rules with defines
# Generate rules for each RV module and architecture combination
define rv_arch_sim_rule
.PRECIOUS: $(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim
$(SIM_BUILD_DIR)/rv_$(1)_$(2)_sim: $(3)/$(1)/$(1).hex $(PRJ_RTL_DIR)/rv_$(1)/rv_$(1)_sim.sv Makefile | $(SIM_BUILD_DIR)
	@$$(IVERILOG) -M $$(@).dep -DRV_$(shell echo $(1) | tr 'a-z' 'A-Z')_HEX='"$(3)/$(1)/$(1).hex"' $$(I_RTL) -I$$(PRJ_TB_DIR) -I$$(PRJ_RTL_DIR)/rv_$(1) -o $$@ $$(word 2,$$^) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		exit $$$${PIPESTATUS[0]}
	@echo "$$@: $$$$(tr '\n' ' ' < $$(@).dep)" > $$(@).d
endef

# Generate rules for each module x architecture
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),i,$(BUILD_DIR)/sw/rv32i)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),im,$(BUILD_DIR)/sw/rv32im)))
$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_arch_sim_rule,$(mod),i_zmmul,$(BUILD_DIR)/sw/rv32i_zmmul)))

# Phony targets for convenience
RV_I_SIMS := $(addprefix rv_,$(addsuffix _i_sim,$(RV_SIM_MODULES)))
RV_IM_SIMS := $(addprefix rv_,$(addsuffix _im_sim,$(RV_SIM_MODULES)))
RV_I_ZMMUL_SIMS := $(addprefix rv_,$(addsuffix _i_zmmul_sim,$(RV_SIM_MODULES)))

.PHONY: $(RV_I_SIMS) $(RV_IM_SIMS) $(RV_I_ZMMUL_SIMS)

$(RV_I_SIMS): rv_%_i_sim: $(SIM_BUILD_DIR)/rv_%_i_sim
	@$(VVP) $< $(if $(filter 1,$(SVC_CPU_DBG)),+SVC_CPU_DBG) $(if $(SVC_SIM_PREFIX),+SVC_SIM_PREFIX,)

$(RV_IM_SIMS): rv_%_im_sim: $(SIM_BUILD_DIR)/rv_%_im_sim
	@$(VVP) $< $(if $(filter 1,$(SVC_CPU_DBG)),+SVC_CPU_DBG) $(if $(SVC_SIM_PREFIX),+SVC_SIM_PREFIX,)

$(RV_I_ZMMUL_SIMS): rv_%_i_zmmul_sim: $(SIM_BUILD_DIR)/rv_%_i_zmmul_sim
	@$(VVP) $< $(if $(filter 1,$(SVC_CPU_DBG)),+SVC_CPU_DBG) $(if $(SVC_SIM_PREFIX),+SVC_SIM_PREFIX,)

# Hex files are built by targeted sw builds (recursive make into sw/<module>)
# The .hex.d files (included above) provide source dependencies for rebuild detection
# Build only the specific program/arch needed rather than all software
define rv_hex_rules
$(BUILD_DIR)/sw/rv32i/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i

$(BUILD_DIR)/sw/rv32im/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32im

$(BUILD_DIR)/sw/rv32i_zmmul/$(1)/$(1).hex:
	@$$(MAKE) -C sw/$(1) RV_ARCH=rv32i_zmmul
endef

$(foreach mod,$(RV_SIM_MODULES),$(eval $(call rv_hex_rules,$(mod))))

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
.PHONY: $(SIM_MODULES)
$(SIM_MODULES): % : $(SIM_BUILD_DIR)/%
	@$(VVP) $< $(if $(filter 1,$(SVC_CPU_DBG)),+SVC_CPU_DBG) $(if $(SVC_SIM_PREFIX),+SVC_SIM_PREFIX,)

# Determine the source subdirectory for each sim
SIM_PRJ_INC = $(PRJ_RTL_DIR)/$(patsubst %_sim,%, $(notdir $(*)))

# Pattern rule to compile a sim
.PRECIOUS: $(SIM_BUILD_DIR)/%
$(SIM_BUILD_DIR)/%: %.sv Makefile | $(SIM_BUILD_DIR)
	@$(IVERILOG) -M $(@).dep $(I_RTL) -I$(PRJ_TB_DIR) -I$(SIM_PRJ_INC) -o $@ $< 2>&1 | \
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

.PHONY: clean_sim
clean_sim:
	@rm -rf $(SIM_BUILD_DIR)

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
	@echo "Available sim targets:"; \
	$(foreach t,$(SIM_MODULES),echo " $t";) \
	echo

list: list_sim

endif
