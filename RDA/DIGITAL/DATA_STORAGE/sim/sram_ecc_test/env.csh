setenv TESTBENCH testrunner
setenv TESTCASE  sram_ecc_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Unit test of SRAM ECC module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_eugene"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED +define+UVM_NO_VERDI_RECORD -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' -P ${VCS_HOME}/include/hdl_xmr.tab"
setenv ANALYZE_OBJECTS	"edf_registers tech/TSMC_180_BCD STD_COMPONENTS DATA_STORAGE/tb/tb_sram_ecc tb_eugene"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS "-ntb_opts uvm -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_MEDIUM +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
