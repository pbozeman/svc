ifndef TOP_MK
TOP_MK := 1

# linting only
.PHONY: lint_top
lint: lint_top

define lint_top_rule
lint_top: lint_$(1)
lint_$(1):
	@$$(LINTER) $(I_RTL) -I$(PRJ_RTL_DIR)/$(patsubst %_top,%, $(notdir $1)) $(1).sv
endef

$(foreach t, $(TOP_MODULES), $(eval $(call lint_top_rule,$(basename $(t)))))

endif
