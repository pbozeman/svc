ifndef ICESTORM_MK
ICESTORM_MK := 1

include mk/dirs.mk

#
# Synthesis, P&R, bitstream gen and programming for lattice ice40 boards.
#

#
# tooling
#

# Yosys
#
# SYNTH_YOSYS allows for varying code based on synthesis under
# icecube2 or yosys
YOSYS_TARGET_DEP = $(BUILD_DIR)/$(notdir $(basename $(@))).dep
YOSYS_TARGET_D   = $(BUILD_DIR)/$(notdir $(basename $(@))).d

YOSYS_FLAGS_DEFS    = -DSYNTH_YOSYS
YOSYS_FLAGS_DEP_GEN = -E $(YOSYS_TARGET_DEP)
YOSYS_FLAGS         = $(YOSYS_FLAGS_DEFS) $(YOSYS_FLAGS_DEP_GEN)
YOSYS               = yosys $(YOSYS_FLAGS)

NEXTPNR := nextpnr-ice40
ICEPACK := icepack
ICEPROG := iceprog

##############################################################################
#
# Synthesis
#
##############################################################################
SYNTH_MODULES := $(basename $(notdir $(TOP_MODULES)))
SYNTH_TARGETS := $(addprefix synth_, $(SYNTH_MODULES))

# humanize the targets rather than .build/bla.json
.PHONY: $(SYNTH_TARGETS)
$(SYNTH_TARGETS): synth_% : $(BUILD_DIR)/%.json

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

endif
