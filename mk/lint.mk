ifndef LINT_MK
LINT_MK := 1

LINTER_SILENT     =
LINTER_FLAGS_DEFS = $(SYNTH_DEFS)
LINTER_FLAGS_WARN = -Wall --Wno-PINCONNECTEMPTY --timing
LINTER_FLAGS_INC  = $(I_RTL) $(I_EXT)
LINTER_FLAGS      = $(LINTER_FLAGS_DEFS) $(LINTER_FLAGS_WARN) $(LINTER_FLAGS_INC)

# External packages that must be compiled before modules that import them
LINTER_EXT_PKGS   = $(EXT_DIR)/common_cells/src/cf_math_pkg.sv \
                    $(EXT_DIR)/fpnew/src/fpnew_pkg.sv
LINTER_EXT_VLT    = $(EXT_DIR)/verilator.vlt

LINTER            = $(LINTER_SILENT)verilator --lint-only --quiet $(LINTER_FLAGS) $(LINTER_EXT_VLT) $(LINTER_EXT_PKGS)

# add targets to 'lint'
.PHONY: lint
lint: LINTER_SILENT = @
lint:

endif
