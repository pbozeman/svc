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
YOSYS_SV         = $(filter %/$*.sv, $(TOP_MODULES))

YOSYS_FLAGS  = -DSYNTH_YOSYS
YOSYS_FLAGS += -E $(YOSYS_TARGET_DEP)
YOSYS_FLAGS += $(YOSYS_FLAGS_DEFS) $(YOSYS_FLAGS_DEP_GEN)
YOSYS = yosys $(YOSYS_FLAGS)

# the synth target pcf is kind of a hack to avoid the fact
# that we can't disable warnings from nextpnr about not
# using all the set_io definitions in a pcf file. We filter
# out the lines not used by the module.
SYNTH_TARGET_PCF = $(BIN_DIR)/$(notdir $(basename $(@))).pcf

#
# Nextprn
#
NEXTPNR_FLAGS  = --$(ICE40_DEVICE) --package $(ICE40_PACKAGE)
NEXTPNR_FLAGS += --freq $(ICE40_CLK_FREQ)
NEXTPNR_FLAGS += --top $(notdir $(basename $@))
NEXTPNR_FLAGS += --pcf $(basename $(@)).pcf
NEXTPNR = nextpnr-ice40 $(NEXTPNR_FLAGS) --json $<

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

# synthesize and generate custom pcf d files
# (the pcf and d generation might be better in a script)
.PRECIOUS: $(BUILD_DIR)/%.json
$(BUILD_DIR)/%.json: | $(BUILD_DIR)
	$(YOSYS) -p '$(call YOSYS_CMD,$(*))'
	@mkdir -p $(BIN_DIR)
	@grep -E "input|output|inout" $(YOSYS_SV) | \
		awk '{gsub(",", "", $$NF); print $$NF}' | \
		grep -v '^$$' | while read -r signal; do \
			grep -E "set_io $${signal}[[:space:]]|set_io $${signal}\\[[0-9:]*\\][[:space:]]" $(PCF_FILE); \
		done > $(SYNTH_TARGET_PCF)
	@cat $(YOSYS_TARGET_DEP) | tr ' ' '\n' | grep -v '^/' | tr '\n' ' ' | \
		awk '{$$1=$$1":"; print}' > $(YOSYS_TARGET_D)

define YOSYS_CMD
read_verilog -sv $(I_RTL) -I$(dir $(YOSYS_SV)) $(YOSYS_SV); \
synth_ice40 -top $(1); \
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

# use a single seed lock for all targets since it's point is to limit
# total parallelism (find_seed already uses all the cores)
SEED_LOCK := $(BUILD_DIR)/.seed_lock
.PRECIOUS: $(BIN_DIR)/%.seed
$(BIN_DIR)/%.seed: $(BUILD_DIR)/%.json
	@mkdir -p $(BIN_DIR)
	@flock -w 30 $(SEED_LOCK) scripts/find_seed.py -o $@ $(NEXTPNR) --asc /dev/null

# pnr
.PRECIOUS: $(BIN_DIR)/%.asc
$(BIN_DIR)/%.asc: $(BUILD_DIR)/%.json $(BIN_DIR)/%.seed
	@mkdir -p $(BIN_DIR)
	$(NEXTPNR) --seed $$(cat $(BIN_DIR)/$(*).seed) --asc $(@)

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
