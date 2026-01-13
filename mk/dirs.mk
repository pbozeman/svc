ifndef DIRS_MK
DIRS_MK := 1

BUILD_DIR  := .build

PRJ_RTL_DIR    := $(PRJ_DIR)/rtl
PRJ_TB_DIR     := $(PRJ_DIR)/tb
PRJ_FORMAL_DIR := $(PRJ_DIR)/tb/formal

SVC_RTL_DIR    := $(SVC_DIR)/rtl
SVC_TB_DIR     := $(SVC_DIR)/tb
SVC_FORMAL_DIR := $(SVC_DIR)/tb/formal
ZIPCPU_FORMAL_DIR := $(SVC_DIR)/tb/formal/private

TOP_DIRS := $(sort $(PRJ_DIR) $(SVC_DIR))
RTL_DIRS := $(foreach d, $(TOP_DIRS), $(d)/rtl)
TB_DIRS := $(foreach d, $(TOP_DIRS), $(d)/tb)
FORMAL_DIRS := $(foreach d, $(TOP_DIRS), $(d)/tb/formal)

# Add RTL and TB subdirectories to include path
# Exclude riscv-formal *_checks directories to avoid argument list too long errors
RTL_SUBDIRS := $(foreach d, $(RTL_DIRS), $(shell find $(d) -type d 2>/dev/null))
TB_SUBDIRS := $(foreach d, $(TB_DIRS), $(shell find $(d) -type d \
    -path '*/riscv-formal/cores/*/*_checks' -prune -o -type d -print 2>/dev/null))

# External dependencies (fpnew and common_cells)
EXT_DIR := $(SVC_DIR)/external
EXT_FPNEW := $(EXT_DIR)/fpnew/src
EXT_COMMON_CELLS_SRC := $(EXT_DIR)/common_cells/src
EXT_COMMON_CELLS_INC := $(EXT_DIR)/common_cells/include
EXT_FPNEW_VENDOR := $(shell find $(EXT_DIR)/fpnew/vendor -type d -name 'rtl' 2>/dev/null)

I_RTL := $(foreach d, $(RTL_DIRS) $(RTL_SUBDIRS), -I$(d))
I_EXT := -I$(EXT_FPNEW) -I$(EXT_COMMON_CELLS_SRC) -I$(EXT_COMMON_CELLS_INC) \
         $(foreach d, $(EXT_FPNEW_VENDOR), -I$(d))
I_TB := $(foreach d, $(TB_DIRS) $(TB_SUBDIRS), -I$(d))
I_FORMAL := $(foreach d, $(FORMAL_DIRS), -I$(d))

endif
