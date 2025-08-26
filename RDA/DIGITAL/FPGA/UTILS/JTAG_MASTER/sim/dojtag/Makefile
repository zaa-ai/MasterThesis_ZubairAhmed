#get TESTCASE from run directory
SHELL := /bin/tcsh

TESTBENCH = tb
F = $(TESTBENCH).f
SIM = $(shell pwd | sed 's%.*/%%')
SIMDIR = /nfs/wrk.$${USER}/sim/$(SIM)

VOPTS = -nc -full64 -sim_res=1ns
EOPTS = -debug_access+all +lint=TFIPC-L -notice 
#EOPTS = +lint=TFIPC-L -notice 
SOPTS = -ucli -i run.tcl
#SOPTS = ""

init:
	-mkdir -p $(SIMDIR)/WORK
	-ln -s $(shell pwd)/* $(SIMDIR)

clean: 
	@-rm -rf $(SIMDIR)/*

analyze: init
	cd $(SIMDIR) && vlogan -full64 -f $(F) | tee analyze.log

elaborate: 
	cd $(SIMDIR) && vcs $(VOPTS) $(EOPTS) $(SDF) $(TESTBENCH) | tee elaborate.log	

simulate: 
	cd $(SIMDIR) && ./simv $(SOPTS) | tee simulate.log

dve:
	cd $(SIMDIR) && dve -replay replay.tcl

all: clean analyze elaborate simulate

help:
	@echo "make <option>"
	@echo "	clean	  : remove content of work directory"
	@echo "	analyze   : nomen est"
	@echo "	elaborate : nomen est"
	@echo "	simulate  : nomen est" 
	@echo "	all 	  : nomen est" 
	@echo "	dve       : open waveform viewer" 

