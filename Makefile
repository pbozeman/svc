# svc Makefile

BUILD_DIR  := .build
RTL_DIR    := rtl
TB_DIR     := tb
FORMAL_DIR := tb/formal
ZIPCPU_FORMAL_DIR := tb/formal/private

RTL := $(wildcard $(RTL_DIR)/*.sv)
RTL_TB := $(wildcard $(TB_DIR)/*_tb.sv)

# Test benches (just the module name)
TEST_BENCHES := $(basename $(notdir $(RTL_TB)))

# Our simulation output files
# These are also the default targets via quick_unit
VCD_FILES := $(addprefix $(BUILD_DIR)/,$(addsuffix .vcd, $(TEST_BENCHES)))

# Formal files
SBY_FILES := $(wildcard $(FORMAL_DIR)/*.sby)
FORMAL_BENCHES := $(basename $(notdir $(SBY_FILES)))
FORMAL_TARGETS := $(addsuffix _f, $(FORMAL_BENCHES))

SYNTH_DEFS := -DSYNTH_YOSYS
ICE40_CELLS_SIM := $(shell yosys-config --datdir/ice40/cells_sim.v)

# Tools
ifneq ($(wildcard tb/formal/private/*.v),)
ZIPCPU_FLAGS := -DZIPCPU_PRIVATE
endif

FORMATTER := scripts/format-sv

IVERILOG_FLAGS_SV   := -g2012
IVERILOG_FLAGS_DEFS := $(SYNTH_DEFS)
IVERILOG_FLAGS_WARN := -Wall -Wno-portbind -Wno-timescale
IVERILOG_FLAGS      := $(IVERILOG_FLAGS_SV) $(IVERILOG_FLAGS_DEFS) $(IVERILOG_FLAGS_WARN)
IVERILOG            := iverilog $(IVERILOG_FLAGS)

LINTER_FLAGS_DEFS := $(SYNTH_DEFS)
LINTER_FLAGS_WARN := -Wall --Wno-PINCONNECTEMPTY --timing
LINTER_FLAGS      := $(LINTER_FLAGS_DEFS) $(LINTER_FLAGS_WARN)
LINTER            := verilator --lint-only --quiet $(LINTER_FLAGS)

# ZIPCPU_FORMAL can't be passed to sby as a flag, the .sby files check
# themselves. But, we do define it above so that linting can be done
# outside of sby
SBY := sby

#
# default target
#
.PHONY: quick
quick: quick_formal .WAIT quick_unit

.PHONY: quick_unit
quick_unit: SKIP_SLOW_TESTS := 1
quick_unit: $(VCD_FILES)

.PHONY: check
check: s_lint unit

# Build dir
$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

# Load previous deps
-include $(wildcard $(BUILD_DIR)/*.d)

##############################################################################
#
# Linting
#
##############################################################################
LINT_FORMAL_FLAGS := -DFORMAL $(ZIPCPU_FLAGS) -I$(FORMAL_DIR) -I$(ZIPCPU_FORMAL_DIR)

.PHONY: lint
lint: s_lint f_lint

.PHONY: s_lint s_lint_% $(addprefix lint_, $(TEST_BENCHES))
s_lint: $(addprefix lint_,$(TEST_BENCHES))

.PHONY: f_lint f_lint_% $(addprefix lint_, $(TEST_BENCHES))
f_lint: $(addprefix f_lint_,$(TEST_BENCHES))

F_LINT_TB_CMD=$(LINTER) -I$(RTL_DIR) -I$(TB_DIR) $(LINT_FORMAL_FLAGS) $(TEST_DIR)$(1).sv
LINT_TB_CMD=$(LINTER) -I$(RTL_DIR) -I$(TB_DIR) $(TEST_DIR)$(1).sv
define lint_tb_rule
lint_$(1):
	@$(LINT_TB_CMD) || (echo $(LINT_TB_CMD); exit 1)
f_lint_$(1):
	@$(F_LINT_TB_CMD) || (echo $(F_LINT_TB_CMD); exit 1)
endef

$(foreach tb, $(TEST_BENCHES), $(eval $(call lint_tb_rule,$(tb))))

##############################################################################
#
# Verification
#
##############################################################################
$(BUILD_DIR)/%: $(TB_DIR)/%.sv $(ICE40_CELLS_SIM) Makefile | $(BUILD_DIR)
	@$(IVERILOG) -M $(@).dep -I$(RTL_DIR) -I$(TB_DIR) -o $@ $(filter-out Makefile,$^)
	@echo "$@: $$(tr '\n' ' ' < $(@).dep)" > $(@).d

.PRECIOUS: $(BUILD_DIR)/%.vcd
$(BUILD_DIR)/%.vcd: $(BUILD_DIR)/%
	@$(VVP) $^ +SKIP_SLOW_TESTS=$(SKIP_SLOW_TESTS) +run=$(RUN) | grep -v "VCD info:"

define run_test
	@$(VVP) $1 +SKIP_SLOW_TESTS=$(SKIP_SLOW_TESTS) +run=$(RUN) 2>&1 |\
		grep -v "VCD info:"; \
		status=$${PIPESTATUS[0]}; \
		if [ $$status -eq 0 ]; then \
			echo "$1" >> $(BUILD_DIR)/tb_success.log; \
		else \
			echo "make $(notdir $1)" >> $(BUILD_DIR)/tb_failure.log; \
		fi
endef

.PHONY: $(TEST_BENCHES)
$(TEST_BENCHES): % : $(BUILD_DIR)/%
	$(call run_test,$<)

# Run all test benches sequentially and show summary
unit: SKIP_SLOW_TESTS := 1
unit: clean_logs $(TEST_BENCHES)
	@echo ""
	@echo "=============================="
	@echo "Successful suites: $$(wc -l < $(BUILD_DIR)/tb_success.log)"
	@echo "Failed suites:     $$(wc -l < $(BUILD_DIR)/tb_failure.log)"
	@sed 's/^/    /' $(BUILD_DIR)/tb_failure.log
	@echo "=============================="

##############################################################################
#
# Formal
#
##############################################################################

# TODO: this only takes a dependency on the immediate .sv file,
# and does so in a brittle way at that since it assumes the .sby and .sv
# file share the same name, which may not be true in the future if multiple
# .sby files target the same .sv file.  The .d files built by iverilog for
# normal verification don't provide sub module dependencies
# here because they all go into a single _tb dependency. But, there is
# surely some mechanism to generate the .d files using iverilog and then
# making sure they are loaded here. The current solution is acceptable,
# for now.
.PRECIOUS: $(BUILD_DIR)/%/status
$(BUILD_DIR)/%/status: $(FORMAL_DIR)/%.sby $(RTL_DIR)/%.sv
	@$(SBY) --prefix .build/$(notdir $*) -f tb/formal/$*.sby
	@touch $@

define run_formal
	@$(SBY) --prefix .build/$(notdir $*)_f -f tb/formal/$*.sby\
		&& echo "$1" >> $(BUILD_DIR)/f_success.log\
		|| echo "make $(notdir $1)" >> $(BUILD_DIR)/f_failure.log
endef

.PHONY: quick_formal
quick_formal: $(foreach b,$(FORMAL_BENCHES),$(BUILD_DIR)/$(b)/status)

$(BUILD_DIR)/%_f:
	@mkdir -p $@

.PHONY: $(FORMAL_TARGETS)
$(FORMAL_TARGETS): %_f : $(BUILD_DIR)/%_f
	$(call run_formal, $<)

# Run all formal benches and show summary
formal: f_lint clean_f_logs $(FORMAL_TARGETS)
	@echo ""
	@echo "=============================="
	@echo "Successful formal: $$(wc -l < $(BUILD_DIR)/f_success.log)"
	@echo "Failed     formal: $$(wc -l < $(BUILD_DIR)/f_failure.log)"
	@sed 's/^/    /' $(BUILD_DIR)/f_failure.log
	@echo "=============================="

##############################################################################
#
# full: lint, unit, formal
#
##############################################################################
full: lint clean_logs clean_f_logs $(FORMAL_TARGETS) .WAIT $(TEST_BENCHES)
	@echo "=============================="
	@echo ""
	@echo "Successful formal: $$(wc -l < $(BUILD_DIR)/f_success.log)"
	@echo "Failed formal:     $$(wc -l < $(BUILD_DIR)/f_failure.log)"
	@sed 's/^/    /' $(BUILD_DIR)/f_failure.log
	@echo ""
	@echo "Successful suites: $$(wc -l < $(BUILD_DIR)/tb_success.log)"
	@echo "Failed suites:     $$(wc -l < $(BUILD_DIR)/tb_failure.log)"
	@sed 's/^/    /' $(BUILD_DIR)/tb_failure.log
	@echo "=============================="

##############################################################################
#
# Formatting
#
##############################################################################
.PHONY: format
format:
	@$(FORMATTER) $(RTL) $(RTL_TB)

##############################################################################
#
# Cleanup
#
##############################################################################
clean:
	@rm -rf $(BUILD_DIR)

clean_logs: $(BUILD_DIR)
	@rm -f $(BUILD_DIR)/tb_success.log $(BUILD_DIR)/tb_failure.log
	@touch $(BUILD_DIR)/tb_success.log $(BUILD_DIR)/tb_failure.log

clean_f_logs: $(BUILD_DIR)
	@rm -f $(BUILD_DIR)/f_success.log $(BUILD_DIR)/f_failure.log
	@touch $(BUILD_DIR)/f_success.log $(BUILD_DIR)/f_failure.log

##############################################################################
#
# Help
#
##############################################################################
.PHONY: list
list:
	@echo "Available unit test targets:"
	@$(foreach t,$(TEST_BENCHES),echo " $t";)
	@echo
	@echo "Available formal test targets:"
	@$(foreach t,$(FORMAL_TARGETS),echo " $t";)
