ifndef RV_FORMAL_MK
RV_FORMAL_MK := 1

include mk/dirs.mk

#
# RISC-V Formal Verification (riscv-formal framework)
# Suffix: _rv_f
#

# Directories
RV_F_DIR := $(PRJ_TB_DIR)/riscv-formal/cores/svc_rv
RV_F_CHECKS_DIR := $(abspath $(PRJ_TB_DIR)/riscv-formal/checks)
RV_F_BUILD_DIR := $(BUILD_DIR)/rvformal

#
# Skip RISC-V formal if the directory doesn't exist (e.g., in consumer projects)
#
ifeq ($(wildcard $(RV_F_DIR)),)

.PHONY: rv_f rv_f_run rv_f_report rv_f_gencheck list_rv_f rv_f_clean
rv_f rv_f_run rv_f_report rv_f_gencheck list_rv_f rv_f_clean:
	@true

define rv_f_quick_report
	@true
endef

else

# Stamp file for gencheck completion
RV_F_GENCHECK_STAMP := $(RV_F_BUILD_DIR)/.gencheck_done

# Key source files for dependency tracking
RV_F_WRAPPER := $(RV_F_DIR)/wrapper.sv
RV_F_CONFIG := $(RV_F_DIR)/config.sv
RV_F_GENCONFIG := $(RV_F_DIR)/generate_configs.sh
RV_F_GENCHECKS := $(RV_F_CHECKS_DIR)/genchecks.py

# RTL dependencies - key RISC-V modules
RV_F_RTL_DEPS := $(wildcard $(PRJ_RTL_DIR)/rv/svc_rv*.sv)

##############################################################################
#
# Config and Check Generation
#
##############################################################################

# Generate .cfg files from template
.PHONY: rv_f_config
rv_f_config: | $(RV_F_BUILD_DIR)
	@cd $(RV_F_DIR) && ./generate_configs.sh > /dev/null

# Generate all check directories and sby files
# This creates *_checks/ directories with *.sby files
.PRECIOUS: $(RV_F_GENCHECK_STAMP)
$(RV_F_GENCHECK_STAMP): $(RV_F_GENCONFIG) $(RV_F_GENCHECKS) $(RV_F_WRAPPER) $(RV_F_CONFIG) $(RV_F_RTL_DEPS) | rv_f_config
	@echo "Generating RISC-V formal checks..."
	@cd $(RV_F_DIR) && \
		for cfg in *_checks.cfg; do \
			name=$${cfg%.cfg}; \
			python3 $(RV_F_CHECKS_DIR)/genchecks.py $$name > /dev/null; \
		done
	@touch $@

.PHONY: rv_f_gencheck
rv_f_gencheck: $(RV_F_GENCHECK_STAMP)

##############################################################################
#
# Dynamic target discovery
#
# After gencheck, we discover all sby files and create targets.
# We use a two-phase approach:
# 1. rv_f_gencheck ensures all sby files exist
# 2. We then glob for them and create targets
#
##############################################################################

# Discover all sby files (will be empty until gencheck runs)
RV_F_SBY_FILES := $(wildcard $(RV_F_DIR)/*_checks/*.sby)

# Extract config and check names: bram_checks/insn_add_ch0.sby -> bram_checks/insn_add_ch0
RV_F_CHECKS := $(patsubst $(RV_F_DIR)/%.sby,%,$(RV_F_SBY_FILES))

# Create target names: bram_checks/insn_add_ch0 -> rv_bram__insn_add_ch0_f
# Remove _checks and use __ as separator between config and check
RV_F_TARGETS := $(foreach c,$(RV_F_CHECKS),rv_$(subst _checks/,__,$(c))_f)

# Create run file paths
RV_F_RUN_FILES := $(patsubst rv_%_f,$(RV_F_BUILD_DIR)/%/ran,$(RV_F_TARGETS))

##############################################################################
#
# RISC-V Formal Execution
#
##############################################################################

.PHONY: rv_f
rv_f: $(RV_F_GENCHECK_STAMP)
	@$(MAKE) rv_f_clean_logs rv_f_run

# Separate target that runs after gencheck so RV_F_SBY_FILES is populated
.PHONY: rv_f_run
rv_f_run: SBY_J := -j1
rv_f_run: $(RV_F_RUN_FILES)
	@if [ -s $(RV_F_BUILD_DIR)/rv_f_failure.log ] && [ -z "$(RV_F_SILENT)" ]; then \
	  echo "=============================="; \
	  $(call rv_f_quick_report) \
	  echo "=============================="; \
	fi

define rv_f_quick_report
	echo "RV Formal dirty   : $$(cat $(RV_F_BUILD_DIR)/rv_f_run.log 2>/dev/null | wc -l)"; \
	echo "RV Formal passed  : $$(cat $(RV_F_BUILD_DIR)/rv_f_success.log 2>/dev/null | wc -l)"; \
	fails=$$(find $(RV_F_BUILD_DIR) -maxdepth 2 -name FAIL 2>/dev/null); \
	cnt=$$(echo "$$fails" | grep -c . || true); \
	echo "RV Formal failed  : $$cnt"; \
	if [ -n "$$fails" ]; then \
		echo "$$fails" | while read f; do \
			tgt=$$(basename $$(dirname "$$f")); \
			echo "    make rv_$${tgt}_f"; \
		done; \
	fi; \
	true
endef

.PHONY: rv_f_report
rv_f_report:
	@echo "==============================";
	@$(call rv_f_quick_report)
	@echo "==============================";

# Pattern rule for running individual checks
# Target: .build/rvformal/<config>_<check>/ran
# Source: tb/riscv-formal/cores/svc_rv/<config>_checks/<check>.sby
.PRECIOUS: $(RV_F_BUILD_DIR)/%/ran
$(RV_F_BUILD_DIR)/%/ran: $(RV_F_GENCHECK_STAMP)
	$(call rv_f_run_check,$*)

# Phony targets for manual execution: make rv_bram__insn_add_ch0_f
.PHONY: $(RV_F_TARGETS)
$(RV_F_TARGETS): rv_%_f : | $(RV_F_GENCHECK_STAMP) $(RV_F_BUILD_DIR)
	$(call rv_f_run_check,$*)

# Convert target name back to paths
# rv_bram__insn_add_ch0_f -> config=bram_checks, check=insn_add_ch0
# Uses __ as separator between config and check
define rv_f_run_check
	$(eval RV_F_TGT := $(1))
	$(eval RV_F_CFG := $(word 1,$(subst __, ,$(RV_F_TGT)))_checks)
	$(eval RV_F_CHK := $(word 2,$(subst __, ,$(RV_F_TGT))))
	@mkdir -p $(RV_F_BUILD_DIR)/$(RV_F_TGT)
	@touch $(RV_F_BUILD_DIR)/rv_f_run.log $(RV_F_BUILD_DIR)/rv_f_success.log $(RV_F_BUILD_DIR)/rv_f_failure.log
	@echo "$(RV_F_TGT)" >> $(RV_F_BUILD_DIR)/rv_f_run.log
	@$(SBY) $(SBY_J) --prefix $(RV_F_BUILD_DIR)/$(RV_F_TGT) -f $(RV_F_DIR)/$(RV_F_CFG)/$(RV_F_CHK).sby \
		&& echo "$(RV_F_TGT)" >> $(RV_F_BUILD_DIR)/rv_f_success.log \
		|| echo "make rv_$(RV_F_TGT)_f" >> $(RV_F_BUILD_DIR)/rv_f_failure.log
	@if [ -f $(RV_F_BUILD_DIR)/$(RV_F_TGT)/FAIL ]; then \
		echo ""; \
		echo "Generate tb:"; \
		echo "./scripts/rvf_to_tb.py $(BUILD_DIR)/rvformal/$(RV_F_TGT)"; \
	fi
	@touch $(RV_F_BUILD_DIR)/$(RV_F_TGT)/ran
endef

define rv_f_full_report
	@echo "RV Formal passed  : $$(cat $(RV_F_BUILD_DIR)/rv_f_success.log 2>/dev/null | wc -l)"
	@fails=$$(find $(RV_F_BUILD_DIR) -maxdepth 2 -name FAIL 2>/dev/null); \
	cnt=$$(echo "$$fails" | grep -c . || true); \
	echo "RV Formal failed  : $$cnt"; \
	if [ -n "$$fails" ]; then \
		echo "$$fails" | while read f; do \
			tgt=$$(basename $$(dirname "$$f")); \
			echo "    make rv_$${tgt}_f"; \
		done; \
	fi; \
	true
endef

.PHONY: rv_f_full_report
rv_f_full_report:
	@echo "=============================="
	$(call rv_f_full_report)
	@echo "=============================="

##############################################################################
#
# Per-config targets: make rv_bram_f, make rv_sram_fwd_f, etc.
#
# Uses recursive make to ensure gencheck runs before targets are resolved
#
##############################################################################

# Extract unique config names from checks (only populated after gencheck)
RV_F_CONFIGS := $(sort $(foreach c,$(RV_F_CHECKS),$(firstword $(subst /, ,$(c)))))

# Internal run targets (only valid after gencheck)
define rv_f_config_run_target
.PHONY: rv_$(patsubst %_checks,%,$(1))_f_run
rv_$(patsubst %_checks,%,$(1))_f_run: $$(filter $(RV_F_BUILD_DIR)/$(patsubst %_checks,%,$(1))__%/ran,$$(RV_F_RUN_FILES))
endef

$(foreach cfg,$(RV_F_CONFIGS),$(eval $(call rv_f_config_run_target,$(cfg))))

# Pattern rule: any rv_*_f target ensures gencheck, then runs
# This allows targets to work even before checks are generated
# Distinguishes config targets (no __) from check targets (with __)
rv_%_f: $(RV_F_GENCHECK_STAMP)
	@$(MAKE) rv_f_clean_logs
	@if echo "$*" | grep -q '__'; then \
		$(MAKE) $(RV_F_BUILD_DIR)/$*/ran; \
	else \
		$(MAKE) rv_$*_f_run; \
	fi

##############################################################################
#
# Build Maintenance
#
##############################################################################

$(RV_F_BUILD_DIR):
	@mkdir -p $@

.PHONY: rv_f_clean_logs
rv_f_clean_logs: | $(RV_F_BUILD_DIR)
	@rm -f $(RV_F_BUILD_DIR)/rv_f_run.log
	@rm -f $(RV_F_BUILD_DIR)/rv_f_success.log
	@rm -f $(RV_F_BUILD_DIR)/rv_f_failure.log
	@touch $(RV_F_BUILD_DIR)/rv_f_run.log
	@touch $(RV_F_BUILD_DIR)/rv_f_success.log
	@touch $(RV_F_BUILD_DIR)/rv_f_failure.log

.PHONY: rv_f_clean
rv_f_clean:
	@rm -rf $(RV_F_BUILD_DIR)
	@rm -rf $(RV_F_DIR)/*_checks/
	@rm -f $(RV_F_DIR)/*_checks.cfg

##############################################################################
#
# Help
#
##############################################################################

.PHONY: list_rv_f
list_rv_f: $(RV_F_GENCHECK_STAMP)
	@echo "Available RISC-V formal configs:"
	@$(foreach cfg,$(RV_F_CONFIGS),echo "  rv_$(patsubst %_checks,%,$(cfg))_f";)
	@echo
	@echo "Individual checks: rv_<config>__<check>_f"
	@echo "Example: make rv_bram__insn_add_ch0_f"
	@echo
	@echo "Total checks: $(words $(RV_F_TARGETS))"

# endif for ifeq ($(wildcard $(RV_F_DIR)),)
endif

##############################################################################
#
# RISC-V Formal Verification (cache-backed svc_rv SoC)
# Suffix: _rv_cache_f
#
##############################################################################

# Directories
RV_CACHE_F_DIR := $(PRJ_TB_DIR)/riscv-formal/cores/svc_rv_cache
RV_CACHE_F_CHECKS_DIR := $(abspath $(PRJ_TB_DIR)/riscv-formal/checks)
RV_CACHE_F_BUILD_DIR := $(BUILD_DIR)/rvformal_cache

#
# Skip cache-backed RISC-V formal if the directory doesn't exist
#
ifeq ($(wildcard $(RV_CACHE_F_DIR)),)

.PHONY: rv_cache_f rv_cache_f_run rv_cache_f_report rv_cache_f_gencheck list_rv_cache_f rv_cache_f_clean
rv_cache_f rv_cache_f_run rv_cache_f_report rv_cache_f_gencheck list_rv_cache_f rv_cache_f_clean:
	@true

define rv_cache_f_quick_report
	@true
endef

else

# Stamp file for gencheck completion
RV_CACHE_F_GENCHECK_STAMP := $(RV_CACHE_F_BUILD_DIR)/.gencheck_done

# Key source files for dependency tracking
RV_CACHE_F_WRAPPER := $(RV_CACHE_F_DIR)/wrapper.sv
RV_CACHE_F_CONFIG := $(RV_CACHE_F_DIR)/config.sv
RV_CACHE_F_GENCONFIG := $(RV_CACHE_F_DIR)/generate_configs.sh
RV_CACHE_F_GENCHECKS := $(RV_CACHE_F_CHECKS_DIR)/genchecks.py

# RTL dependencies - key cache and RV modules
RV_CACHE_F_RTL_DEPS := $(wildcard $(PRJ_RTL_DIR)/rv/svc_rv*.sv) \
	$(wildcard $(PRJ_RTL_DIR)/common/svc_cache_axi*.sv) \
	$(wildcard $(PRJ_RTL_DIR)/axi/svc_axi_*.sv)

##############################################################################
#
# Config and Check Generation
#
##############################################################################

# Generate .cfg files from template
.PHONY: rv_cache_f_config
rv_cache_f_config: | $(RV_CACHE_F_BUILD_DIR)
	@cd $(RV_CACHE_F_DIR) && ./generate_configs.sh > /dev/null

# Generate all check directories and sby files
.PRECIOUS: $(RV_CACHE_F_GENCHECK_STAMP)
$(RV_CACHE_F_GENCHECK_STAMP): $(RV_CACHE_F_GENCONFIG) $(RV_CACHE_F_GENCHECKS) $(RV_CACHE_F_WRAPPER) $(RV_CACHE_F_CONFIG) $(RV_CACHE_F_RTL_DEPS) | rv_cache_f_config
	@echo "Generating RISC-V cache formal checks..."
	@cd $(RV_CACHE_F_DIR) && \
		for cfg in *_checks.cfg; do \
			name=$${cfg%.cfg}; \
			python3 $(RV_CACHE_F_CHECKS_DIR)/genchecks.py $$name > /dev/null; \
		done
	@touch $@

.PHONY: rv_cache_f_gencheck
rv_cache_f_gencheck: $(RV_CACHE_F_GENCHECK_STAMP)

##############################################################################
#
# Dynamic target discovery
#
##############################################################################

# Discover all sby files (will be empty until gencheck runs)
RV_CACHE_F_SBY_FILES := $(wildcard $(RV_CACHE_F_DIR)/*_checks/*.sby)

# Extract config and check names: icache_checks/insn_add_ch0.sby -> icache_checks/insn_add_ch0
RV_CACHE_F_CHECKS := $(patsubst $(RV_CACHE_F_DIR)/%.sby,%,$(RV_CACHE_F_SBY_FILES))

# Create target names: icache_checks/insn_add_ch0 -> rv_cache_icache__insn_add_ch0_f
RV_CACHE_F_TARGETS := $(foreach c,$(RV_CACHE_F_CHECKS),rv_cache_$(subst _checks/,__,$(c))_f)

# Create run file paths
RV_CACHE_F_RUN_FILES := $(patsubst rv_cache_%_f,$(RV_CACHE_F_BUILD_DIR)/%/ran,$(RV_CACHE_F_TARGETS))

##############################################################################
#
# RISC-V Cache Formal Execution
#
##############################################################################

.PHONY: rv_cache_f
rv_cache_f: $(RV_CACHE_F_GENCHECK_STAMP)
	@$(MAKE) rv_cache_f_clean_logs rv_cache_f_run

.PHONY: rv_cache_f_run
rv_cache_f_run: SBY_J := -j1
rv_cache_f_run: $(RV_CACHE_F_RUN_FILES)
	@if [ -s $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_failure.log ] && [ -z "$(RV_F_SILENT)" ]; then \
	  echo "=============================="; \
	  $(call rv_cache_f_quick_report) \
	  echo "=============================="; \
	fi

define rv_cache_f_quick_report
	echo "RV Cache Formal dirty   : $$(cat $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_run.log 2>/dev/null | wc -l)"; \
	echo "RV Cache Formal passed  : $$(cat $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_success.log 2>/dev/null | wc -l)"; \
	fails=$$(find $(RV_CACHE_F_BUILD_DIR) -maxdepth 2 -name FAIL 2>/dev/null); \
	cnt=$$(echo "$$fails" | grep -c . || true); \
	echo "RV Cache Formal failed  : $$cnt"; \
	if [ -n "$$fails" ]; then \
		echo "$$fails" | while read f; do \
			tgt=$$(basename $$(dirname "$$f")); \
			echo "    make rv_cache_$${tgt}_f"; \
		done; \
	fi; \
	true
endef

.PHONY: rv_cache_f_report
rv_cache_f_report:
	@echo "==============================";
	@$(call rv_cache_f_quick_report)
	@echo "==============================";

# Pattern rule for running individual checks
.PRECIOUS: $(RV_CACHE_F_BUILD_DIR)/%/ran
$(RV_CACHE_F_BUILD_DIR)/%/ran: $(RV_CACHE_F_GENCHECK_STAMP)
	$(call rv_cache_f_run_check,$*)

# Phony targets for manual execution: make rv_cache_icache__insn_add_ch0_f
.PHONY: $(RV_CACHE_F_TARGETS)
$(RV_CACHE_F_TARGETS): rv_cache_%_f : | $(RV_CACHE_F_GENCHECK_STAMP) $(RV_CACHE_F_BUILD_DIR)
	$(call rv_cache_f_run_check,$*)

# Convert target name back to paths
define rv_cache_f_run_check
	$(eval RV_CACHE_F_TGT := $(1))
	$(eval RV_CACHE_F_CFG := $(word 1,$(subst __, ,$(RV_CACHE_F_TGT)))_checks)
	$(eval RV_CACHE_F_CHK := $(word 2,$(subst __, ,$(RV_CACHE_F_TGT))))
	@mkdir -p $(RV_CACHE_F_BUILD_DIR)/$(RV_CACHE_F_TGT)
	@touch $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_run.log $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_success.log $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_failure.log
	@echo "$(RV_CACHE_F_TGT)" >> $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_run.log
	@$(SBY) $(SBY_J) --prefix $(RV_CACHE_F_BUILD_DIR)/$(RV_CACHE_F_TGT) -f $(RV_CACHE_F_DIR)/$(RV_CACHE_F_CFG)/$(RV_CACHE_F_CHK).sby \
		&& echo "$(RV_CACHE_F_TGT)" >> $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_success.log \
		|| echo "make rv_cache_$(RV_CACHE_F_TGT)_f" >> $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_failure.log
	@if [ -f $(RV_CACHE_F_BUILD_DIR)/$(RV_CACHE_F_TGT)/FAIL ]; then \
		echo ""; \
		echo "Generate tb:"; \
		echo "./scripts/rvf_to_tb.py $(BUILD_DIR)/rvformal_cache/$(RV_CACHE_F_TGT)"; \
	fi
	@touch $(RV_CACHE_F_BUILD_DIR)/$(RV_CACHE_F_TGT)/ran
endef

##############################################################################
#
# Per-config targets: make rv_cache_icache_f, make rv_cache_dcache_f, etc.
#
##############################################################################

# Extract unique config names from checks (only populated after gencheck)
RV_CACHE_F_CONFIGS := $(sort $(foreach c,$(RV_CACHE_F_CHECKS),$(firstword $(subst /, ,$(c)))))

# Internal run targets (only valid after gencheck)
define rv_cache_f_config_run_target
.PHONY: rv_cache_$(patsubst %_checks,%,$(1))_f_run
rv_cache_$(patsubst %_checks,%,$(1))_f_run: $$(filter $(RV_CACHE_F_BUILD_DIR)/$(patsubst %_checks,%,$(1))__%/ran,$$(RV_CACHE_F_RUN_FILES))
endef

$(foreach cfg,$(RV_CACHE_F_CONFIGS),$(eval $(call rv_cache_f_config_run_target,$(cfg))))

# Pattern rule: any rv_cache_*_f target ensures gencheck, then runs
rv_cache_%_f: $(RV_CACHE_F_GENCHECK_STAMP)
	@$(MAKE) rv_cache_f_clean_logs
	@if echo "$*" | grep -q '__'; then \
		$(MAKE) $(RV_CACHE_F_BUILD_DIR)/$*/ran; \
	else \
		$(MAKE) rv_cache_$*_f_run; \
	fi

##############################################################################
#
# Build Maintenance
#
##############################################################################

$(RV_CACHE_F_BUILD_DIR):
	@mkdir -p $@

.PHONY: rv_cache_f_clean_logs
rv_cache_f_clean_logs: | $(RV_CACHE_F_BUILD_DIR)
	@rm -f $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_run.log
	@rm -f $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_success.log
	@rm -f $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_failure.log
	@touch $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_run.log
	@touch $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_success.log
	@touch $(RV_CACHE_F_BUILD_DIR)/rv_cache_f_failure.log

.PHONY: rv_cache_f_clean
rv_cache_f_clean:
	@rm -rf $(RV_CACHE_F_BUILD_DIR)
	@rm -rf $(RV_CACHE_F_DIR)/*_checks/
	@rm -f $(RV_CACHE_F_DIR)/*_checks.cfg

##############################################################################
#
# Help
#
##############################################################################

.PHONY: list_rv_cache_f
list_rv_cache_f: $(RV_CACHE_F_GENCHECK_STAMP)
	@echo "Available RISC-V cache formal configs:"
	@$(foreach cfg,$(RV_CACHE_F_CONFIGS),echo "  rv_cache_$(patsubst %_checks,%,$(cfg))_f";)
	@echo
	@echo "Individual checks: rv_cache_<config>__<check>_f"
	@echo "Example: make rv_cache_icache__insn_add_ch0_f"
	@echo
	@echo "Total checks: $(words $(RV_CACHE_F_TARGETS))"

# endif for ifeq ($(wildcard $(RV_CACHE_F_DIR)),)
endif

endif
