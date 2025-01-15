ifndef ICESTORM_MK
ICESTORM_MK := 1

include mk/dirs.mk

#
# Synthesis, P&R, bitstream gen and programming for lattice ice40 boards.
#
ifeq ($(ICE40_DEV_BOARD),)
$(error ICE40_DEV_BOARD is not set)
endif

ifeq ($(ICE40_DEVICE),)
$(error ICE40_DEVICE is not set)
endif

ifeq ($(ICE40_PACKAGE),)
$(error ICE40_PACKAGE is not set)
endif

ifeq ($(CONSTRAINTS_DIR),)
$(error CONSTRAINTS_DIR is not set)
endif

BIN_DIR  = $(BUILD_DIR)/$(ICE40_DEV_BOARD)-$(ICE40_DEVICE)-$(ICE40_PACKAGE)
PCF_FILE = $(CONSTRAINTS_DIR)/$(ICE40_DEV_BOARD)-$(ICE40_DEVICE)-$(ICE40_PACKAGE).pcf

# Yosys
#
# SYNTH_YOSYS allows for varying code based on synthesis under
# icecube2 or yosys
YOSYS_TARGET_DEP = $(basename $(@)).dep
YOSYS_TARGET_D   = $(basename $(@)).d

YOSYS_FLAGS  = -DSYNTH_YOSYS
YOSYS_FLAGS += -E $(YOSYS_TARGET_DEP)
YOSYS_FLAGS += $(YOSYS_FLAGS_DEFS) $(YOSYS_FLAGS_DEP_GEN)
YOSYS = yosys $(YOSYS_FLAGS)

#
# Nextprn
#
NEXTPNR_FLAGS  = --$(ICE40_DEVICE) --package $(ICE40_PACKAGE)
NEXTPNR_FLAGS += --freq $(ICE40_CLK_FREQ)
NEXTPNR_FLAGS += --top $(notdir $(basename $@))
NEXTPNR_FLAGS += --pcf $(PCF_FILE)
NEXTPNR = nextpnr-ice40 $(NEXTPNR_FLAGS) --json $< --asc

#
# Icepack/prog
#
ICEPACK := icepack
ICEPROG := iceprog

##############################################################################
#
# Synthesis
#
##############################################################################
SYNTH_MODULES := $(basename $(notdir $(TOP_MODULES)))
SYNTH_TARGETS := $(addsuffix _synth, $(SYNTH_MODULES))

# humanize the targets rather than .build/bla.json
.PHONY: $(SYNTH_TARGETS)
$(SYNTH_TARGETS): %_synth : $(BUILD_DIR)/%.json

# synthesize and generate d files
.PRECIOUS: $(BUILD_DIR)/%.json
$(BUILD_DIR)/%.json: | $(BUILD_DIR)
	$(YOSYS) -p '$(strip $(call YOSYS_CMD,$(*)))'
	@cat $(YOSYS_TARGET_DEP) | tr ' ' '\n' | grep -v '^/' | tr '\n' ' ' | \
		awk '{$$1=$$1":"; print}' > $(YOSYS_TARGET_D)

# looking the module back up in top modules is a bit weird, but it
# vastly simplifies the rules before this. The alternative is to iterate
# over the top modules and use a define to generate rules dynamically,
# but that approach greatly complicates the path management logic,
# rather than isolating the wonkiness to a single place as is done here.
# The trade off is that top modules have to have unique names,
# even if they are in different directories.
define YOSYS_CMD
read_verilog -sv $(I_RTL)                          \
  -I$(dir $(filter %/$*.sv, $(TOP_MODULES)))       \
  $(filter %/$*.sv, $(TOP_MODULES));               \
synth_ice40 -top $(1);                             \
write_json $@
endef

.PHONY: synth
synth: $(SYNTH_TARGETS)

# aliases
.PHONY: synthesis
synthesis: synth

##############################################################################
#
# P&R
#
##############################################################################
PNR_TARGETS := $(addsuffix _pnr, $(SYNTH_MODULES))

# humanize the targets
.PHONY: $(PNR_TARGETS)
$(PNR_TARGETS): %_pnr : $(BIN_DIR)/%.asc

# pnr
.PRECIOUS: $(BIN_DIR)/%.asc
$(BIN_DIR)/%.asc: $(BUILD_DIR)/%.json
	@mkdir -p $(BIN_DIR)
	$(NEXTPNR) $@

.PHONY: pnr
pnr: $(PNR_TARGETS)

##############################################################################
#
# Bitstream
#
##############################################################################
BIN_TARGETS := $(addsuffix _bin, $(SYNTH_MODULES))

# humanize the targets
.PHONY: $(BIN_TARGETS)
$(BIN_TARGETS): %_bin : $(BIN_DIR)/%.bin

# bistream gen
.PRECIOUS: $(BIN_DIR)/%.bin
$(BIN_DIR)/%.bin: $(BIN_DIR)/%.asc
	$(ICEPACK) $< $@

.PHONY: bin
bin: $(BIN_TARGETS)

# alias
.PHONY: bits
bits: bin

##############################################################################
#
# Programming
#
##############################################################################
PROG_TARGETS := $(addsuffix _prog,$(SYNTH_MODULES))

%_prog: $(BIN_DIR)/%.bin
	$(ICEPROG) $<

.PHONY: list_prog
list_prog:
	@echo "Available prog targets:"
	@$(foreach t,$(PROG_TARGETS),echo " $t";)
endif
