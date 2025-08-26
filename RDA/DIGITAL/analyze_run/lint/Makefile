###############################################################################
# (C) COPYRIGHT 2022 ELMOS  AG ALL RIGTHS RESERVED                            
# Date:         12.12.2022
# Author:       makoe
# Description:  Makefile flow SpyGlass LINT
  VERSION = 0.1
#
# History:
# Date          Version     Author  Description
# 12.12.2022    0.1         makoe   initial version
###############################################################################

###############################################################################
# General Setup
###############################################################################

THIS_TARGET = $@

ifdef GUI
  SPY_OPTIONS += -gui -run
else
  SPY_OPTIONS += -batch
endif

FOLDERS = ./results ./reports

###############################################################################
# Project Specific Setup
###############################################################################

TOP_MODULE    = $(shell getPrjCfg.rb name)
TECH          = $(shell getPrjCfg.rb -p tech)
GATES_LIB     = $(shell getPrjCfg.rb -r ${TECH} -p tech/lib/typ | sed 's:/db/:/liberty/:' | sed 's:\.db:\.lib:')
SOURCE_LIST   = ./results/digital.f

###############################################################################
# Targets
###############################################################################

#==============================================================================
help:
#==============================================================================
	@echo "*******************************************************************************"
	@echo " Makefile Flow for SpyGlass LINT"
	@echo " Version ${VERSION}"
	@echo " "
	@echo " Help Text"
	@echo "*******************************************************************************"
	@echo " "
	@echo " usage: make <TARGET>"
	@echo " "
	@echo " Available Targets:"
	@echo "==============================================================================="
	@echo " clean                           remove all"
	@echo " help                            displays help text"
	@echo " info                            displays license information"
	@echo " lint                            run lint check"
	@echo " debug                           run GUI to debug results"
	@echo " "
	@echo " Available Options:"
	@echo "==============================================================================="
	@echo " GUI=1                           Interactive Mode"
	@echo " "
	@echo "==============================================================================="

#==============================================================================
info:
#==============================================================================
	@echo "*******************************************************************************"
	@echo " Makefile Flow for MeridianCDC and iDebug"
	@echo " Version ${VERSION}"
	@echo " "
	@echo " License Information"
	@echo "*******************************************************************************"
	@echo "-------------------------------------------------------------------------------"
	@echo " SpyGlass:"
	@echo "-------------------------------------------------------------------------------"
	lmstat -f BasePolicySO

#==============================================================================
clean:
#==============================================================================
	rm -rf $(FOLDERS)
	rm -rf command.log default.svf
#==============================================================================
prepare: $(FOLDERS)
#==============================================================================
	@echo "### generate list of files... "
	mkdir -p results
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name files.f -and -not -path *tb_eugene/files.f -a -not -path */results/files.f > results/files.f
	@find ${PROJECT_HOME}/tech/TSMC_180_BCD/hdl -maxdepth 1 -name files.f >> results/files.f
	perl ../script/create_lof.pl
	
#==============================================================================
lint: prepare 
#==============================================================================
	spyglass -project user_tcl/spyglass_lint.prj -goal lint/lint_rtl $(SPY_OPTIONS)
	@rm -rf WORK

#==============================================================================
debug:
#==============================================================================
	spyglass -project user_tcl/spyglass_lint.prj -goal lint/lint_rtl -gui
	@rm -rf gui_command.log

#==============================================================================
$(FOLDERS):
#==============================================================================
	@echo "Creating Folder \"$@\""
	@mkdir -p $@

###############################################################################
# export all variables to sub processes
###############################################################################
.EXPORT_ALL_VARIABLES:
