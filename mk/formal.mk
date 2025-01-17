ifndef FORMAL_MK
FORMAL_MK := 1

include mk/dirs.mk
include mk/format.mk
include mk/iverilog.mk
include mk/lint.mk

# Formal sources and modules
F_SV := $(wildcard $(PRJ_FORMAL_DIR)/*.sv)
F_SBY := $(wildcard $(PRJ_FORMAL_DIR)/*.sby)
F_MODULES := $(basename $(notdir $(F_SBY)))
F_TARGETS := $(addsuffix _f, $(F_MODULES))

ifneq ($(wildcard tb/formal/private/*.v),)
ZIPCPU_FLAGS := -DZIPCPU_PRIVATE
endif

# Formal output
F_BUILD_DIR := $(BUILD_DIR)/formal

SBY := sby

##############################################################################
#
# Formal Formatting & Linting
#
##############################################################################
format: format_f

.PHONY: format_f
format_f:
	@$(FORMATTER) $(F_SV)

# Add all the combos of conditional flags for linting as it's easy
# to mess up in the modules and leave out a condition and have an unused
# or undriven signal
.PHONY: lint_f lint_fm lint_fz lint_fzm
lint: lint_f lint_fm lint_fz lint_fzm

LINT_FLAGS_FORMAL = $(SVC_FORMAL_DIR)/verilator.vlt -DFORMAL $(I_TB) $(I_FORMAL)
LINT_FLAGS_FORMAL_ZIPCPU = $(LINT_FLAGS_FORMAL) $(ZIPCPU_FLAGS) -I$(ZIPCPU_FORMAL_DIR)

define lint_f_rule
.PHONY: lint_f_$(1)
lint_f: lint_f_$(1)
lint_f_$(1):
	$$(LINTER) $$(LINT_FLAGS_FORMAL) $1

.PHONY: lint_fm_$(1)
lint_fm: lint_fm_$(1)
lint_fm_$(1):
	$$(LINTER) $$(LINT_FLAGS_FORMAL) -DFORMAL_$(shell echo "$1" | tr a-z A-Z) $1

.PHONY: lint_fz_$(1)
lint_fz: lint_fz_$(1)
lint_fz_$(1):
	$$(LINTER) $$(LINT_FLAGS_FORMAL_ZIPCPU) $1

.PHONY: lint_fzm_$(1)
lint_fzm: lint_fzm_$(1)
lint_fzm_$(1):
	$$(LINTER) $$(LINT_FLAGS_FORMAL_ZIPCPU) -DFORMAL_$(shell echo "$1" | tr a-z A-Z) $1
endef

$(foreach tb, $(F_MODULES), $(eval $(call lint_f_rule,$(tb))))

##############################################################################
#
# Formal Verification
#
##############################################################################
F_RUN_FILES := $(addprefix $(F_BUILD_DIR)/,$(addsuffix _f/ran, $(F_MODULES)))

.PHONY: formal
formal: f_clean_logs $(F_RUN_FILES)
	@if [ -s $(F_BUILD_DIR)/f_failure.log ] && [ -z "$(F_SILENT)" ]; then \
	  echo "=============================="; \
	  $(call f_quick_report)                 \
	  echo "=============================="; \
	fi

define f_quick_report
	echo "Formal dirty    : $$(wc -l < $(F_BUILD_DIR)/f_run.log)"; \
	echo "Formal passed   : $$(wc -l < $(F_BUILD_DIR)/f_success.log)"; \
	echo "Formal failed   : $$(wc -l < $(F_BUILD_DIR)/f_failure.log)"; \
	sed 's/^/    /' $(F_BUILD_DIR)/f_failure.log;
endef

.PHONY: f_report
f_report:
	@echo "==============================";
	@$(call f_quick_report)
	@echo "==============================";

.PRECIOUS: $(F_BUILD_DIR)/%_f/ran
$(F_BUILD_DIR)/%_f/ran: $(PRJ_FORMAL_DIR)/%.sby $(F_BUILD_DIR)/%_f $(F_BUILD_DIR)/%_f/ran.d
	$(call f_run_formal,$*)

.PHONY: $(F_TARGETS)
$(F_TARGETS): %_f : $(F_BUILD_DIR)/%_f
	$(call f_run_formal,$*)

define f_run_formal
	@echo "$1" >> $(F_BUILD_DIR)/f_run.log
	@$(SBY) --prefix $(F_BUILD_DIR)/$1_f -f $(PRJ_FORMAL_DIR)/$1.sby\
		&& echo "$1" >> $(F_BUILD_DIR)/f_success.log\
		|| echo "make $1_f" >> $(F_BUILD_DIR)/f_failure.log
	@touch $(F_BUILD_DIR)/$1_f/ran
endef

# create dependencies for future runs
.PRECIOUS: $(F_BUILD_DIR)/%_f/ran.dep
$(F_BUILD_DIR)/%_f/ran.dep: $(PRJ_RTL_DIR)/%.sv
	@mkdir -p $(dir $(@))
	@$(IVERILOG) -M $(@) -DNO_SB_IO $(I_RTL) $(I_TB) -o /dev/null $^

.PRECIOUS: $(F_BUILD_DIR)/%_f/ran.d
$(F_BUILD_DIR)/%_f/ran.d: $(F_BUILD_DIR)/%_f/ran.dep
	@echo "$(F_BUILD_DIR)/$*_f/ran: $$(tr '\n' ' ' < $(F_BUILD_DIR)/$*_f/ran.dep)" > $(@)

# Run all test benches sequentially and show summary
.PHONY: f_run
f_run: SKIP_SLOW_TESTS := 1
f_run: lint_f f_clean_logs $(F_TARGETS)

define f_full_report
	@echo "Formal    passed: $$(wc -l < $(F_BUILD_DIR)/f_success.log)"
	@echo "Formal    failed: $$(wc -l < $(F_BUILD_DIR)/f_failure.log)"
	@sed 's/^/    /' $(F_BUILD_DIR)/f_failure.log
endef

.PHONY: f_full_report
f_full_report:
	@echo "=============================="
	$(call f_full_report)
	@echo "=============================="

.PHONY: f_full
f_full: f_run .WAIT f_report

# aliases
.PHONY: formal_run
formal_run: f_run

.PHONY: formal_full_report
formal_report: f_full_report

.PHONY: formal_full
formal_full: f_full

##############################################################################
#
# Build Maintenance
#
##############################################################################
$(F_BUILD_DIR):
	@mkdir -p $(@)

.PRECIOUS: $(F_BUILD_DIR)/%_f
$(F_BUILD_DIR)/%_f:
	@mkdir -p $@

clean_logs: f_clean_logs

.PHONY: f_clean_logs
f_clean_logs: | $(F_BUILD_DIR)
	@rm -f $(F_BUILD_DIR)/f_run.log
	@rm -f $(F_BUILD_DIR)/f_success.log
	@rm -f $(F_BUILD_DIR)/f_failure.log
	@touch $(F_BUILD_DIR)/f_run.log
	@touch $(F_BUILD_DIR)/f_success.log
	@touch $(F_BUILD_DIR)/f_failure.log

##############################################################################
#
# Help
#
##############################################################################
.PHONY: list_f
list_f:
	@echo "Available formal targets:"
	@$(foreach t,$(F_TARGETS),echo " $t";)
	@echo
endif
