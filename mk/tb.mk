ifndef TB_MK
TB_MK := 1

include mk/dirs.mk
include mk/format.mk
include mk/lint.mk
include mk/iverilog.mk

ICE40_CELLS_SIM := $(shell yosys-config --datdir/ice40/cells_sim.v)

##############################################################################
#
# TB Discovery
#
# Two types of testbenches:
#   *_tbi.sv - Icarus Verilog (fast compilation, default)
#   *_tbv.sv - Verilator (advanced SV features like fpnew)
#
##############################################################################
TBI_SV := $(shell find $(PRJ_TB_DIR) -name '*_tbi.sv' 2>/dev/null)
TBI_MODULES := $(basename $(notdir $(TBI_SV)))
TBI_SUBDIRS := $(shell find $(PRJ_TB_DIR) -type d 2>/dev/null)

TBV_SV := $(shell find $(PRJ_TB_DIR) -name '*_tbv.sv' 2>/dev/null)
TBV_MODULES := $(basename $(notdir $(TBV_SV)))
TBV_SUBDIRS := $(shell find $(PRJ_TB_DIR) -type d 2>/dev/null)

# Tell Make where to find tb files
vpath %_tbi.sv $(TBI_SUBDIRS)
vpath %_tbv.sv $(TBV_SUBDIRS)

# Build directories
TBI_BUILD_DIR := $(BUILD_DIR)/tbi
TBV_BUILD_DIR := $(BUILD_DIR)/tbv
TB_BUILD_DIR := $(BUILD_DIR)/tb

# C++ wrapper for Verilator TBs
TB_MAIN_CPP := $(SVC_DIR)/tb/cpp/tb_main.cpp

# Other mk groups can take a dependency on tb_pass
TB_PASS_FILE := $(TB_BUILD_DIR)/pass
.PHONY: tb_pass
tb_pass: $(TB_PASS_FILE)

##############################################################################
#
# Shared Verilator Runtime (for tbv)
#
# Build verilator support files once and share across all testbenches.
# This avoids recompiling verilated.cpp, verilated_timing.cpp, etc. for
# each testbench, significantly reducing build time.
#
##############################################################################
VERILATOR_ROOT := $(shell verilator --getenv VERILATOR_ROOT)
VERILATOR_INC := $(VERILATOR_ROOT)/include
VL_RT_DIR := $(BUILD_DIR)/verilator_rt

# Compiler flags matching what Verilator uses
VL_RT_CXXFLAGS := -I$(VERILATOR_INC) -I$(VERILATOR_INC)/vltstd
VL_RT_CXXFLAGS += -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TIMING=1
VL_RT_CXXFLAGS += -DVM_TRACE=0 -DVM_TRACE_FST=0 -DVM_TRACE_VCD=0
VL_RT_CXXFLAGS += -faligned-new -fcf-protection=none
VL_RT_CXXFLAGS += -Wno-bool-operation -Wno-shadow -Wno-sign-compare
VL_RT_CXXFLAGS += -Wno-subobject-linkage -Wno-tautological-compare
VL_RT_CXXFLAGS += -Wno-uninitialized -Wno-unused-but-set-parameter
VL_RT_CXXFLAGS += -Wno-unused-but-set-variable -Wno-unused-parameter
VL_RT_CXXFLAGS += -Wno-unused-variable -fcoroutines -Os

# Runtime object files
VL_RT_OBJS := $(VL_RT_DIR)/verilated.o
VL_RT_OBJS += $(VL_RT_DIR)/verilated_timing.o
VL_RT_OBJS += $(VL_RT_DIR)/verilated_threads.o

# Static library for the runtime
VL_RT_LIB := $(VL_RT_DIR)/libverilated_rt.a

$(VL_RT_DIR):
	@mkdir -p $@

$(VL_RT_DIR)/verilated.o: | $(VL_RT_DIR)
	@g++ $(VL_RT_CXXFLAGS) -c -o $@ $(VERILATOR_INC)/verilated.cpp

$(VL_RT_DIR)/verilated_timing.o: | $(VL_RT_DIR)
	@g++ $(VL_RT_CXXFLAGS) -c -o $@ $(VERILATOR_INC)/verilated_timing.cpp

$(VL_RT_DIR)/verilated_threads.o: | $(VL_RT_DIR)
	@g++ $(VL_RT_CXXFLAGS) -c -o $@ $(VERILATOR_INC)/verilated_threads.cpp

$(VL_RT_LIB): $(VL_RT_OBJS)
	@ar rcs $@ $^

.PHONY: verilator_rt
verilator_rt: $(VL_RT_LIB)

# Verilator TB command (without --build, we do our own build step)
# tbv tests enable EXT_F=1 since they're for advanced SV features like fpnew
VERILATOR_TB_FLAGS := --cc --exe --timing -DEXT_F=1
VERILATOR_TB_FLAGS += -Wall -Wno-PINCONNECTEMPTY -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM
VERILATOR_TB_FLAGS += -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-TIMESCALEMOD -Wno-GENUNNAMED
VERILATOR_TB_FLAGS += -Wno-ASCRANGE -Wno-UNSIGNED -Wno-UNOPTFLAT
VERILATOR_TB_FLAGS += -O3
VERILATOR_TB_FLAGS += $(I_RTL) $(I_EXT) $(I_TB)
VERILATOR_TB := verilator $(VERILATOR_TB_FLAGS)

# fpnew source files for Verilator builds (in dependency order)
# Packages must come first in correct order
FPNEW_CF_PKG := $(SVC_DIR)/external/common_cells/src/cf_math_pkg.sv
FPNEW_PKG := $(SVC_DIR)/external/fpnew/src/fpnew_pkg.sv
FPNEW_COMMON := $(filter-out %cf_math_pkg.sv,$(wildcard $(SVC_DIR)/external/common_cells/src/*.sv))
FPNEW_SRC := $(filter-out %fpnew_pkg.sv,$(wildcard $(SVC_DIR)/external/fpnew/src/*.sv))
FPNEW_VENDOR := $(wildcard $(SVC_DIR)/external/fpnew/vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/*.v)
FPNEW_SRCS := $(FPNEW_CF_PKG) $(FPNEW_PKG) $(FPNEW_COMMON) $(FPNEW_VENDOR) $(FPNEW_SRC)

##############################################################################
#
# TB Formatting & Linting
#
##############################################################################
format: format_tbi format_tbv

.PHONY: format_tbi
format_tbi:
ifneq ($(TBI_SV),)
	@$(FORMATTER) $(TBI_SV)
endif

.PHONY: format_tbv
format_tbv:
ifneq ($(TBV_SV),)
	@$(FORMATTER) $(TBV_SV)
endif

.PHONY: lint_tbi lint_tbv
lint: lint_tbi lint_tbv

define lint_tbi_rule
lint_tbi: lint_$(1)
lint_$(1):
	@$$(LINTER) $(SVC_TB_DIR)/verilator.vlt $(I_TB) -I$(PRJ_RTL_DIR)/$(patsubst %_tbi,%, $(notdir $1)) $(1).sv
endef

# Suppressions for fpnew external library warnings
FPNEW_LINT_FLAGS := -Wno-UNOPTFLAT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-UNSIGNED \
	-Wno-TIMESCALEMOD -Wno-GENUNNAMED -Wno-ASCRANGE -Wno-UNUSEDPARAM -Wno-UNUSEDSIGNAL

define lint_tbv_rule
lint_tbv: lint_$(1)
lint_$(1):
	@$$(LINTER) $(SVC_TB_DIR)/verilator.vlt $(I_TB) $(I_EXT) -I$(PRJ_RTL_DIR)/$(patsubst %_tbv,%, $(notdir $1)) \
		$(FPNEW_LINT_FLAGS) $(1).sv
endef

$(foreach tb, $(TBI_MODULES), $(eval $(call lint_tbi_rule,$(tb))))
$(foreach tb, $(TBV_MODULES), $(eval $(call lint_tbv_rule,$(tb))))

##############################################################################
#
# TB Pass Files
#
##############################################################################
TBI_PASS_FILES := $(addprefix $(TBI_BUILD_DIR)/,$(addsuffix .pass, $(TBI_MODULES)))
TBV_PASS_FILES := $(addprefix $(TBV_BUILD_DIR)/,$(addsuffix .pass, $(TBV_MODULES)))

##############################################################################
#
# TB Execution - Common
#
##############################################################################

# run a tb and do results tracking
# $1 = executable path, $2 = pass file path (optional, defaults to $1.pass)
define tb_run_test
	@echo "$1" >> $(TB_BUILD_DIR)/tb_run.log;
	@$1 +SKIP_SLOW_TESTS=$(SKIP_SLOW_TESTS) +run=$(RUN) +SVC_TB_RPT=$(SVC_TB_RPT) $(if $(SVC_RV_DBG_CPU),+SVC_RV_DBG_CPU=$(SVC_RV_DBG_CPU)) $(if $(SVC_RV_DBG_IF),+SVC_RV_DBG_IF=$(SVC_RV_DBG_IF)) $(if $(SVC_RV_DBG_ID),+SVC_RV_DBG_ID=$(SVC_RV_DBG_ID)) $(if $(SVC_RV_DBG_EX),+SVC_RV_DBG_EX=$(SVC_RV_DBG_EX)) $(if $(SVC_RV_DBG_MEM),+SVC_RV_DBG_MEM=$(SVC_RV_DBG_MEM)) $(if $(SVC_RV_DBG_WB),+SVC_RV_DBG_WB=$(SVC_RV_DBG_WB)) $(if $(SVC_RV_DBG_HAZ),+SVC_RV_DBG_HAZ=$(SVC_RV_DBG_HAZ)) $(if $(SVC_RV_DBG_RVFI),+SVC_RV_DBG_RVFI=$(SVC_RV_DBG_RVFI)) 2>&1 |\
		grep -v "VCD info:" |\
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored"; \
		status=$${PIPESTATUS[0]}; \
		if [ $$status -eq 0 ]; then \
			if [ -z "$(RUN)" ]; then \
				touch "$(or $2,$1.pass)"; \
			fi; \
			echo "$1" >> $(TB_BUILD_DIR)/tb_success.log; \
		else \
			echo "make $$(basename $$(dirname $1))" >> $(TB_BUILD_DIR)/tb_failure.log; \
		fi
endef

define tb_quick_report
	echo "TB dirty          : $$(cat $(TB_BUILD_DIR)/tb_run.log 2>/dev/null | wc -l)"; \
	echo "TB passed         : $$(cat $(TB_BUILD_DIR)/tb_success.log 2>/dev/null | wc -l)"; \
	echo "TB failed         : $$(cat $(TB_BUILD_DIR)/tb_failure.log 2>/dev/null | wc -l)"; \
	sed 's/^/    /' $(TB_BUILD_DIR)/tb_failure.log 2>/dev/null || true;
endef

.PHONY: tb_report
tb_report:
	@echo "==============================";
	@$(call tb_quick_report)
	@echo "==============================";

##############################################################################
#
# Icarus Verilog Testbenches (_tbi)
#
##############################################################################

# Generate build and run rules for each Icarus testbench
define tbi_rules
# Build rule for $(1)
.PRECIOUS: $(TBI_BUILD_DIR)/$(1)/$(1)
$(TBI_BUILD_DIR)/$(1)/$(1): $(1).sv $(ICE40_CELLS_SIM) Makefile | $(TBI_BUILD_DIR)
	@mkdir -p $(TBI_BUILD_DIR)/$(1)
	@$$(IVERILOG) -M $(TBI_BUILD_DIR)/$(1).dep $$(I_RTL) $$(I_EXT) $$(I_TB) \
		-I$(PRJ_RTL_DIR)/$(patsubst %_tbi,%,$(1)) \
		-o $$@ $$< $(ICE40_CELLS_SIM) 2>&1 | \
		grep -v "vvp.tgt sorry: Case unique/unique0 qualities are ignored" >&2; \
		test $$$${PIPESTATUS[0]} -eq 0
	@echo "$$@:" $$$$(cat $(TBI_BUILD_DIR)/$(1).dep) > $(TBI_BUILD_DIR)/$(1).d

# Pass file rule for $(1)
$(TBI_BUILD_DIR)/$(1).pass: $(TBI_BUILD_DIR)/$(1)/$(1) | $(TB_BUILD_DIR)
	$$(call tb_run_test,$$<,$$@)

# Phony target to run $(1)
.PHONY: $(1)
$(1): $(TBI_BUILD_DIR)/$(1)/$(1) | $(TB_BUILD_DIR)
	$$(call tb_run_test,$$<)
endef

$(foreach tb,$(TBI_MODULES),$(eval $(call tbi_rules,$(tb))))

##############################################################################
#
# Verilator Testbenches (_tbv)
#
##############################################################################

# Generate build and run rules for each Verilator testbench
define tbv_rules
# Build rule for $(1)
.PRECIOUS: $(TBV_BUILD_DIR)/$(1)/V$(1)
$(TBV_BUILD_DIR)/$(1)/V$(1): $(1).sv $(TB_MAIN_CPP) $(VL_RT_LIB) Makefile | $(TBV_BUILD_DIR)
	@mkdir -p $(TBV_BUILD_DIR)/$(1)
	@$$(IVERILOG) -M $(TBV_BUILD_DIR)/$(1).dep -o /dev/null \
		$$(I_RTL) $$(I_EXT) $$(I_TB) -I$(PRJ_RTL_DIR)/$(patsubst %_tbv,%,$(1)) $$< 2>/dev/null || true
	@echo "$$@:" $$$$(cat $(TBV_BUILD_DIR)/$(1).dep) > $(TBV_BUILD_DIR)/$(1).d
	@$$(VERILATOR_TB) \
		-I$(PRJ_RTL_DIR)/$(patsubst %_tbv,%,$(1)) \
		--Mdir $(TBV_BUILD_DIR)/$(1) \
		--top-module $(1) \
		-CFLAGS '-DTB_HEADER=\"V$(1).h\" -DTB_TOP=V$(1)' \
		$(FPNEW_SRCS) $$< $(TB_MAIN_CPP)
	@$$(MAKE) -s -C $(TBV_BUILD_DIR)/$(1) -f V$(1).mk \
		VK_GLOBAL_OBJS="" \
		VM_PREFIX=V$(1) \
		LDLIBS="$(abspath $(VL_RT_LIB))" \
		V$(1)

# Pass file rule for $(1)
$(TBV_BUILD_DIR)/$(1).pass: $(TBV_BUILD_DIR)/$(1)/V$(1) | $(TB_BUILD_DIR)
	$$(call tb_run_test,$$<,$$@)

# Phony target to run $(1)
.PHONY: $(1)
$(1): $(TBV_BUILD_DIR)/$(1)/V$(1) | $(TB_BUILD_DIR)
	$$(call tb_run_test,$$<)
endef

$(foreach tb,$(TBV_MODULES),$(eval $(call tbv_rules,$(tb))))

# Include generated dependency files
-include $(wildcard $(TBI_BUILD_DIR)/*.d)
-include $(wildcard $(TBV_BUILD_DIR)/*.d)

##############################################################################
#
# Main Targets
#
##############################################################################
.PHONY: tb tbi tbv
tb: SKIP_SLOW_TESTS := 1
tb: tb_clean_logs tbi tbv
	@if [ -s $(TB_BUILD_DIR)/tb_failure.log ] || [ -z "$(SILENT_SUCCESS)" ]; then \
	  echo "=============================="; \
	  $(call tb_quick_report)                \
	  echo "=============================="; \
	fi
	@[ ! -s $(TB_BUILD_DIR)/tb_failure.log ] || exit 1;

tbi: SKIP_SLOW_TESTS := 1
tbi: tb_clean_logs $(TBI_PASS_FILES)

tbv: SKIP_SLOW_TESTS := 1
tbv: tb_clean_logs $(TBV_PASS_FILES)

# the pass file for all tests
$(TB_BUILD_DIR)/pass: tb
	@if [ ! -s $(TB_BUILD_DIR)/tb_failure.log ]; then \
	  touch $(TB_BUILD_DIR)/pass; \
	else \
	  exit 1; \
	fi

# Run all test benches sequentially and show summary
.PHONY: tb_run
tb_run: SKIP_SLOW_TESTS := 1
tb_run: lint_tbi lint_tbv tb_clean_logs $(TBI_MODULES) $(TBV_MODULES)

define tb_full_report
	@echo "TB passed         : $$(cat $(TB_BUILD_DIR)/tb_success.log 2>/dev/null | wc -l)"
	@echo "TB failed         : $$(cat $(TB_BUILD_DIR)/tb_failure.log 2>/dev/null | wc -l)"
	@sed 's/^/    /' $(TB_BUILD_DIR)/tb_failure.log 2>/dev/null || true
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
$(TBI_BUILD_DIR):
	@mkdir -p $(@)

$(TBV_BUILD_DIR):
	@mkdir -p $(@)

$(TB_BUILD_DIR):
	@mkdir -p $(@)
	@touch $(TB_BUILD_DIR)/tb_run.log
	@touch $(TB_BUILD_DIR)/tb_success.log
	@touch $(TB_BUILD_DIR)/tb_failure.log

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
.PHONY: list_tb list_tbi list_tbv
list_tb: list_tbi list_tbv

list_tbi:
	@echo "Available Icarus (tbi) targets:"
	@$(foreach t,$(TBI_MODULES),echo " $t";)
	@echo

list_tbv:
	@echo "Available Verilator (tbv) targets:"
	@$(foreach t,$(TBV_MODULES),echo " $t";)
	@echo

endif
