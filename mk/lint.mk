ifndef LINT_MK
LINT_MK := 1

LINTER_SILENT     =
LINTER_FLAGS_DEFS = $(SYNTH_DEFS)
LINTER_FLAGS_WARN = -Wall --Wno-PINCONNECTEMPTY --timing
LINTER_FLAGS_INC  = $(I_RTL) $(I_EXT)
LINTER_FLAGS      = $(LINTER_FLAGS_DEFS) $(LINTER_FLAGS_WARN) $(LINTER_FLAGS_INC)
LINTER            = $(LINTER_SILENT)verilator --lint-only --quiet $(LINTER_FLAGS)

# add targets to 'lint'
.PHONY: lint
lint: LINTER_SILENT = @
lint:

endif
