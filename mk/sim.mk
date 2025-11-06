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
