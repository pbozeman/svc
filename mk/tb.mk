ifndef TB_MK
TB_MK := 1

include mk/dirs.mk
include mk/format.mk
include mk/lint.mk

ICE40_CELLS_SIM := $(shell yosys-config --datdir/ice40/cells_sim.v)

# TB sources and modules
TB_SV := $(shell find $(PRJ_TB_DIR) -name '*_tb.sv' 2>/dev/null)
TB_MODULES := $(basename $(notdir $(TB_SV)))
TB_SUBDIRS := $(shell find $(PRJ_TB_DIR) -type d 2>/dev/null)

# Tell Make where to find _tb.sv files
vpath %_tb.sv $(TB_SUBDIRS)

# TB output
TB_BUILD_DIR := $(BUILD_DIR)/tb
TB_PASS_FILE := $(TB_BUILD_DIR)/pass

# Other mk groups can take a dependency on tb_pass
.PHONY: tb_pass
tb_pass: $(TB_PASS_FILE)

##############################################################################
#
# TB Formatting & Linting
#
##############################################################################
format: format_tb

.PHONY: format_tb
format_tb:
	@$(FORMATTER) $(TB_SV)

.PHONY: lint_tb
lint: lint_tb

define lint_tb_rule
lint_tb: lint_$(1)
lint_$(1):
	@$$(LINTER) $(I_TB) -I$(PRJ_RTL_DIR)/$(patsubst %_tb,%, $(notdir $1)) $(1).sv
endef

$(foreach tb, $(TB_MODULES), $(eval $(call lint_tb_rule,$(tb))))

##############################################################################
#
# TB Execution
#
##############################################################################
TB_PASS_FILES := $(addprefix $(TB_BUILD_DIR)/,$(addsuffix .pass, $(TB_MODULES)))

.PHONY: tb
tb: SKIP_SLOW_TESTS := 1
tb: tb_clean_logs $(TB_PASS_FILES)
	@if [ -s $(TB_BUILD_DIR)/tb_failure.log ] || [ -z "$(SILENT_SUCCESS)" ]; then \
	  echo "=============================="; \
	  $(call tb_quick_report)                \
	  echo "=============================="; \
	fi
	@[ ! -s $(TB_BUILD_DIR)/tb_failure.log ] || exit 1;

define tb_quick_report
	echo "TB suites dirty : $$(wc -l < $(TB_BUILD_DIR)/tb_run.log)"; \
	echo "TB suites passed: $$(wc -l < $(TB_BUILD_DIR)/tb_success.log)"; \
	echo "TB suites failed: $$(wc -l < $(TB_BUILD_DIR)/tb_failure.log)"; \
	sed 's/^/    /' $(TB_BUILD_DIR)/tb_failure.log;
endef

.PHONY: tb_report
tb_report:
	@echo "==============================";
	@$(call tb_quick_report)
	@echo "==============================";

# the pass file for the all tests
$(TB_BUILD_DIR)/pass: tb
	@if [ ! -s $(TB_BUILD_DIR)/tb_failure.log ]; then \
	  touch $(TB_BUILD_DIR)/pass; \
	else \
	  exit 1; \
	fi

# individual tb pass files
$(TB_BUILD_DIR)/%.pass: $(TB_BUILD_DIR)/%
	$(call tb_run_test,$<)

# simulation "synthesis"
TB_PRJ_INC = $(PRJ_RTL_DIR)/$(patsubst %_tb,%, $(notdir $(*)))
.PRECIOUS: $(TB_BUILD_DIR)/%
$(TB_BUILD_DIR)/%: %.sv $(ICE40_CELLS_SIM) Makefile | $(TB_BUILD_DIR)
	@$(IVERILOG) -M $(@).dep $(I_RTL) $(I_TB) -I$(TB_PRJ_INC) -o $@ $< $(ICE40_CELLS_SIM) 2>&1 | grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		test $${PIPESTATUS[0]} -eq 0
	@echo "$@: $$(tr '\n' ' ' < $(@).dep)" > $(@).d

# run a tb and do results tracking
define tb_run_test
	@echo "$1" >> $(TB_BUILD_DIR)/tb_run.log;
	@$(VVP) $1 +SKIP_SLOW_TESTS=$(SKIP_SLOW_TESTS) +run=$(RUN) +SVC_TB_RPT=$(SVC_TB_RPT) $(if $(filter 1,$(SVC_CPU_DBG)),+SVC_CPU_DBG) 2>&1 |\
		grep -v "VCD info:" |\
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored"; \
		status=$${PIPESTATUS[0]}; \
		if [ $$status -eq 0 ]; then \
			if [ -z "$(RUN)" ]; then \
				touch "$1".pass; \
			fi; \
			echo "$1" >> $(TB_BUILD_DIR)/tb_success.log; \
		else \
			echo "make $(notdir $1)" >> $(TB_BUILD_DIR)/tb_failure.log; \
		fi
endef

# Helper to run a _tb, recompiling it first if necessary.
# Not depending on .pass and forcing a re-run is intentional to allow manual
# forcing of re-execution, mainly during tb_full.
.PHONY: $(TB_MODULES)
$(TB_MODULES): % : $(TB_BUILD_DIR)/%
	$(call tb_run_test,$<)

# Run all test benches sequentially and show summary
.PHONY: tb_run
tb_run: SKIP_SLOW_TESTS := 1
tb_run: lint_tb tb_clean_logs $(TB_MODULES)

define tb_full_report
	@echo "TB suites passed: $$(wc -l < $(TB_BUILD_DIR)/tb_success.log)"
	@echo "TB suites failed: $$(wc -l < $(TB_BUILD_DIR)/tb_failure.log)"
	@sed 's/^/    /' $(TB_BUILD_DIR)/tb_failure.log
endef

.PHONY: tb_full_report
tb_full_report:
	@echo "=============================="
	$(call tb_report)
	@echo "=============================="

.PHONY: tb_full
tb_full: tb_run .WAIT tb_report

# aliases
.PHONY: unit
unit: tb

.PHONY: unit_full
unit_full: tb_full

##############################################################################
#
# Build Maintenance
#
##############################################################################
$(TB_BUILD_DIR):
	@mkdir -p $(@)

clean_logs: tb_clean_logs

.PHONY: tb_clean_logs
tb_clean_logs: | $(TB_BUILD_DIR)
	@rm -f $(TB_BUILD_DIR)/tb_run.log
	@rm -f $(TB_BUILD_DIR)/tb_success.log
	@rm -f $(TB_BUILD_DIR)/tb_failure.log
	@touch $(TB_BUILD_DIR)/tb_run.log
	@touch $(TB_BUILD_DIR)/tb_success.log
	@touch $(TB_BUILD_DIR)/tb_failure.log

##############################################################################
#
# Help
#
##############################################################################
.PHONY: list_tb
list_tb:
	@echo "Available tb targets:"
	@$(foreach t,$(TB_MODULES),echo " $t";)
	@echo

endif
