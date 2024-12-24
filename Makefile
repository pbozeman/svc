# svc Makefile

RTL_DIR := rtl
RTL := $(wildcard $(RTL_DIR)/*.sv)

# Tools
FORMATTER := scripts/format-sv

##############################################################################
#
# Formatting
#
##############################################################################
.PHONY: format
format:
	@$(FORMATTER) $(RTL)
