###############################################################################
# (C) COPYRIGHT 2022 ELMOS  AG ALL RIGTHS RESERVED                            
# Date:         12.12.2022
# Author:       makoe
# Description:  Makefile flow SpyGlass LINT
# VERSION = 0.1
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

#TOP_MODULE    = $(shell getPrjCfg.rb name)
TOP_MODULE    = asic_shell
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
	@echo " Makefile Flow for SpyGlass DFT"
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
	@echo " "
	@echo " dft_scan_ready                  run TestMaxAdvisor goal dft_scan_ready"
	@echo "                                 Validate that flip-flops in the design"
	@echo "                                 meet scannability requirements"
	@echo " "
	@echo " dft_best_practice               run TestMaxAdvisor dft_best_practice"
	@echo "                                 Best coding practices to maximize ATPG"
	@echo "                                 coverage and ATPG efficiency"
	@echo " "
	@echo " dft_dft_dsm_random_resistance   run TestMaxAdvisor dft_best_practice"
	@echo "                                 Identify random resistant logic"
	@echo "                                 (i.e. hard to test with ATPG patterns)"
	@echo " "
	@echo " dft_dsm_best_practice           run TestMaxAdvisor goal dft_best_practice"
	@echo "                                 Analyze transition coverage and"
	@echo "                                 best practices to maximize it"
	@echo " "
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
	@echo " Makefile Flow for SpyGlass DFT"
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
	rm -rf default.svf command.log
	rm -rf DIGITAL_comp JTAG_comp OTP_MEM_comp spyglass.out

#==============================================================================
prepare: $(FOLDERS)
#==============================================================================
	@echo "### generate list of files... "
	mkdir -p results
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name files.f -and -not -path *tb_eugene/files.f -a -not -path */results/files.f > results/files.f
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name otp_mem_vhdl* >> results/files.f
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name digital_vhdl_pkg.f >> results/files.f
	@find ${PROJECT_HOME}/*/ -maxdepth 1 -name jtag_vhdl.f   >> results/files.f
	@find ${PROJECT_HOME}/tech/TSMC_180_BCD/hdl -maxdepth 1 -name files.f >> results/files.f
	@find ${PROJECT_HOME}/be_run/test/hdl -maxdepth 1 -name files.f >> results/files.f
	perl ../script/create_lof.pl

#==============================================================================
dft_scan_ready: prepare $(FOLDERS)
#==============================================================================
	spyglass -project user_tcl/spyglass_dft.prj -goal dft/dft_scan_ready $(SPY_OPTIONS)
	@rm -rf WORK

#==============================================================================
dft_best_practice: prepare $(FOLDERS)
#==============================================================================
	spyglass -project user_tcl/spyglass_dft.prj -goal "dft/dft_scan_ready,dft/dft_best_practice" $(SPY_OPTIONS)
	@rm -rf WORK

#==============================================================================
dft_dft_dsm_random_resistance: prepare $(FOLDERS)
#==============================================================================
	spyglass -project user_tcl/spyglass_dft.prj -goal "dft/dft_scan_ready,dft/dft_best_practice,dft/dft_dft_dsm_random_resistance" $(SPY_OPTIONS)
	@rm -rf WORK

#==============================================================================
dft_dsm_best_practice: prepare $(FOLDERS)
#==============================================================================
	spyglass -project user_tcl/spyglass_dft.prj -goal "dft/dft_scan_ready,dft/dft_best_practice,dft/dft_dsm_random_resistance,dft/dft_dsm_best_practice" $(SPY_OPTIONS)
	@rm -rf WORK

#==============================================================================
debug:
#==============================================================================
	spyglass -project user_tcl/spyglass_dft.prj -goal dft/dft_scan_ready -gui
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
