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

I_RTL := $(foreach d, $(RTL_DIRS), -I$(d))
I_TB := $(foreach d, $(TB_DIRS), -I$(d))
I_FORMAL := $(foreach d, $(FORMAL_DIRS), -I$(d))

endif
