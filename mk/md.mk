ifndef MD_MK
MD_MK := 1

MD_FORMATTER := prettier --prose-wrap always --print-width 80 --write
MD_FILES := $(shell find . -name "*.md" -type f)

.PHONY: mdformat
mdformat:
	@$(MD_FORMATTER) $(MD_FILES)

format: mdformat

endif
