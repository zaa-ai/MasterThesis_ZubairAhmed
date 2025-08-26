###############################################################################
# (C) COPYRIGHT 2021 ELMOS  AG ALL RIGTHS RESERVED                            
# Date:         06.12.2021
# Author:       erv
# Description:  Makefile flow for Meridian RDC
  VERSION = 0.2
#
# History:
# Date          Version     Author  Description
# 12.12.2022    0.2         makoe   unified environment for lint/cdc/rdc
# 06.12.2021    0.1         erv     initial version
###############################################################################

###############################################################################
# General Setup
###############################################################################

THIS_TARGET = $@

ifndef SDC
 SDC = func_min
endif

ifndef CASE
 SCENARIO = ${SDC}
else
 SCENARIO = ${SDC}_${CASE}
endif

FOLDERS = ./results ./reports ./logs

###############################################################################
# Project Specific Setup
###############################################################################

TOP_MODULE    = $(shell getPrjCfg.rb name)
TECH          = $(shell getPrjCfg.rb -p tech)
GATES_LIB     = $(shell getPrjCfg.rb -r ${TECH} -p tech/lib/typ | sed 's:/db/:/liberty/:' | sed 's:\.db:\.lib:')
INPUT_DRIVER  = $(shell getPrjCfg.rb -r ${TECH} tech/phys/sdc_driving_cell)
SOURCE_LIST   = results/digital.f

###############################################################################
# Targets
###############################################################################

#==============================================================================
help:
#==============================================================================
	@echo "*******************************************************************************"
	@echo " Makefile Flow for MeridianRDC and iDebug"
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
	@echo " rdc                             run rdc check"
	@echo " debug                           run GUI to debug results"
	@echo " "
	@echo " Available Options:"
	@echo "==============================================================================="
	@echo " SDF=<name>                     [REQUIRED] defines the SDC scenario <name>"
	@echo "                                           e.g.: func_min, scan_min, ..."
	@echo " CASE=<name>                    [OPTIONAL] defines the meridian case <name>"
	@echo "                                           e.g.: default, case1, case2, ..."
	@echo " "
	@echo "==============================================================================="

#==============================================================================
info:
#==============================================================================
	@echo "*******************************************************************************"
	@echo " Makefile Flow for MeridianRDC and iDebug"
	@echo " Version ${VERSION}"
	@echo " "
	@echo " License Information"
	@echo "*******************************************************************************"
	@echo "-------------------------------------------------------------------------------"
	@echo " Meridian:"
	@echo "-------------------------------------------------------------------------------"
	lmstat -f VerixCDCBase
	lmstat -f MeridianRDCBase
	lmstat -f IntentVision

#==============================================================================
clean:
#==============================================================================
	rm -rf $(FOLDERS)

#==============================================================================
prepare: $(FOLDERS)
#==============================================================================
	@echo "### generate list of files... "
	mkdir -p results
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name files.f -and -not -path *tb_eugene/files.f -a -not -path */results/files.f > results/files.f
	@find ${PROJECT_HOME}/tech/TSMC_180_BCD/hdl -maxdepth 1 -name files.f >> results/files.f
	perl ../script/create_lof.pl

#==============================================================================
rdc: prepare
#==============================================================================
	mrdc -i user_tcl/meridian_rdc.tcl -project ./results/${TOP_MODULE}_${SCENARIO} -session ${SCENARIO} -l logs/vrdc.log
ifeq ($(GUI), 1)
	@make debug
endif

#==============================================================================
debug:
#==============================================================================
	idebug -project ./results/${TOP_MODULE}_${SCENARIO} -log logs/idebug.log
	rm -rf idebugFiles .idebugrc ivision.ws

#==============================================================================
$(FOLDERS):
#==============================================================================
	@echo "Creating Folder \"$@\""
	@mkdir -p $@

################################################################################################################
# export all variables to sub processes
################################################################################################################
.EXPORT_ALL_VARIABLES:

