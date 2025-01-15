ifndef RTL_MK
RTL_MK := 1

RTL_SV := $(wildcard $(PRJ_RTL_DIR)/*.sv)

##############################################################################
#
# Formatting (linting happens via tb and tops)
#
##############################################################################
format: format_rtl

.PHONY: format_rtl
format_rtl:
	@$(FORMATTER) $(RTL_SV)

endif
