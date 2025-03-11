ifndef MD_MK
MD_MK := 1

MD_FORMATTER := mdformat --wrap 80
MD_FILES := $(shell find . -name "*.md" -type f)

.PHONY: mdformat
mdformat:
	@$(MD_FORMATTER) $(MD_FILES)

format: mdformat

endif
