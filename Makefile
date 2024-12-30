# svc Makefile

BUILD_DIR  := .build
RTL_DIR    := rtl
TB_DIR     := tb
FORMAL_DIR := formal

RTL := $(wildcard $(RTL_DIR)/*.sv)
RTL_TB := $(wildcard $(TB_DIR)/*_tb.sv)

# Test benches (just the module name)
TEST_BENCHES := $(basename $(notdir $(RTL_TB)))

# Our simulation output files
# These are also the default targets via quick_unit
VCD_FILES := $(addprefix $(BUILD_DIR)/,$(addsuffix .vcd, $(TEST_BENCHES)))

SYNTH_DEFS := -DSYNTH_YOSYS

# Tools
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

#
# default target
#
.PHONY: quick_unit
quick_unit: SKIP_SLOW_TESTS := 1
quick_unit: $(VCD_FILES)

.PHONY: check
check: lint unit

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
.PHONY: lint lint_% $(addprefix lint_, $(TEST_BENCHES))
lint: $(addprefix lint_,$(TEST_BENCHES))

LINT_TB_CMD=$(LINTER) -I$(RTL_DIR) -I$(TB_DIR) -I$(FORMAL_DIR) $(TEST_DIR)$(1).sv
define lint_tb_rule
lint_$(1):
	@$(LINT_TB_CMD) || (echo $(LINT_TB_CMD); exit 1)
endef

$(foreach tb, $(TEST_BENCHES), $(eval $(call lint_tb_rule,$(tb))))

##############################################################################
#
# Verification
#
##############################################################################
$(BUILD_DIR)/%: $(TB_DIR)/%.sv Makefile | $(BUILD_DIR)
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
	@echo "Failed suites: $$(wc -l < $(BUILD_DIR)/tb_failure.log)"
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
