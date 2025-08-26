.DEFAULT_GOAL := fpga_batch

#SYNOPSYS_DIR = "/common/run/synopsys/designcompiler/P-2019.03-SP5-6"

ifndef DEBUGCORE
 DEBUGCORE=0
endif

ifdef NO_REPORTS
 NO_REPORTS_COM = -tclargs no_reports
endif
detected_OS = $(shell uname -r)
not_runing_on_kernel_version = 2.6.32-431.29.2.el6.x86_64

fpga: files
#fpga: clean

ifeq ($(detected_OS),$(not_runing_on_kernel_version))
	@echo "#########################################################################"
	@echo "# Vivado will not run on this OS, please switch to newer CentOS servers #"
	@echo "#########################################################################"
else
	@echo "### start vivado FPGA synthesis... "
	export DEBUGCORE=$(DEBUGCORE); vivado -source xsyn.tcl $(NO_REPORTS_COM) &
endif

fpga_batch: files
#fpga_batch: clean

ifeq ($(detected_OS),$(not_runing_on_kernel_version))
	@echo "#########################################################################"
	@echo "# Vivado will not run on this OS, please switch to newer CentOS servers #"
	@echo "#########################################################################"
else
	@echo "### start vivado FPGA synthesis... "
	export DEBUGCORE=$(DEBUGCORE); vivado -mode batch -source xsyn.tcl $(NO_REPORTS_COM)
endif

files: clean
	@echo "### generate list of files... "
	mkdir -p results
	@find -L ../../* -name "files.f" | grep -v /tb_* | grep -v /model | grep -v /be_run | grep -v /sim | grep -v /tech/TSMC_180_BCD | grep -v /analyze_run > results/files.f
	@find ../../tech/TSMC_180_BCD/ip/ROM_Nibble/models/ -name "tcb018gbwp7t_rom.v"  > results/inc.lof
	@find -L ../../tech/ -name "*.sv" -o -name "*.v" -o -name "*.vhd" | grep -v /tb | grep -v _tb | grep -v /derive/ >> results/inc.lof
	@find -L ../../config -name "*.sv" -o -name "*.v" -o -name "*.vhd" | grep -v /tb | grep -v _tb | grep -v /derive/ >> results/inc.lof
	@find -L ../../*     -name "*_inst.sv" -o -name "*_inst.v"         | grep -v /tb | grep -v _tb | grep -v /derive/ >> results/inc.lof
	@find -L ../inc/     -name "*.sv" -o -name "*.v" -o -name "*.vhd"  | grep /inc | grep -v /tb | grep -v _tb | grep -v /derive/ >> results/inc.lof
	@find -L ../UTILS/   -name "*.sv" -o -name "*.v" -o -name "*.vhd"  | grep /inc | grep -v /tb | grep -v _tb | grep -v /derive/ >> results/inc.lof
	@find -L ../../ECC/rtl  -name "*_inc.sv"   | grep /rtl | grep -v /tb | grep -v _tb  >> results/inc.lof
	#@find -L $(SYNOPSYS_DIR)/dw/sim_ver -name "*.sv" -o -name "*.v" -o -name "*.vhd"   >> results/inc.lof
	perl ./create_lof.pl

clean:
	@echo "### remove vivado files... "
	rm -f vivado*
	rm -f fsm_encoding.os
	rm -f post_syn.dcp
	rm -f *.mmi
	rm -f webtalk.jou
	rm -f webtalk.log
	rm -f checkpoint_1.dcp
	rm -rf .Xil
	rm -rf .cache
	rm -rf xgd_oracle*
	rm -rf results/*	
	rm -f usage_statistics_webtalk.*
	rm -rf mcs

zip:
	@echo  52143_FPGA_`date +'%Y%m%d.%H%M%S'`
	zip -r results/52143_FPGA_`date +'%Y%m%d'` results/FPGA.*

help:
	@echo "Only running on CentOS Servers!"
	@echo ""
	@echo "make files                    # (re-)generate design files"
	@echo ""
	@echo "make clean                    # remove vivado files"
	@echo ""
	@echo "make fpga                     # syn FPGA design"
	@echo ""
	@echo "make fpga NO_REPORTS=1        # syn FPGA design without report generation (speeds up the flow)"
	@echo ""
	@echo "make fpga_batch               # syn FPGA design in batch mode"
	@echo ""
