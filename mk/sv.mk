ifndef SV_MK

MAKEFLAGS += -I$(dir $(realpath $(lastword $(MAKEFILE_LIST))))/..

include mk/formal.mk
include mk/format.mk
include mk/iverilog.mk
include mk/rtl.mk
include mk/tb.mk

##############################################################################
#
# default target (quick test run)
#
##############################################################################
.PHONY: quick
quick: SILENT_SUCCESS := 1
quick: tb .WAIT formal .WAIT report

.PHONY:
report:
	@echo "=============================="
	@$(call tb_quick_report)
	@echo
	@$(call f_quick_report)
	@echo "=============================="

# Load previous deps
DEPS := $(shell find $(BUILD_DIR) -name '*.d' 2>/dev/null)
-include $(DEPS)

##############################################################################
#
# full: lint, tb, formal
#
##############################################################################
.PHONY: full_run
full_run: tb_run .WAIT f_run

.PHONY: full_report
full_report:
	@echo "=============================="
	$(call tb_full_report)
	@echo
	$(call f_full_report)
	@echo "=============================="

full: SILENT_SUCCESS := 1
full: lint clean_logs .WAIT full_run .WAIT full_report

##############################################################################
#
# Build Maintenance
#
##############################################################################
$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

.PHONY: clean
clean:
	@rm -rf $(BUILD_DIR)

.PHONY: clean_logs
clean_logs: $(BUILD_DIR)

##############################################################################
#
# Help
#
##############################################################################
.PHONY: list_tb list_f list_prog

.PHONY: list
list: list_tb .WAIT list_f .WAIT list_prog
endif
