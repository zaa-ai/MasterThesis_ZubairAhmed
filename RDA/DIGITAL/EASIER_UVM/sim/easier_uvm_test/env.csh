setenv TESTBENCH testrunner
setenv TESTCASE  easier_uvm_test
setenv TC_DESCRIPTION "Unit test of Eugene UVM Testbench and its classes"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_eugene"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' +define+RUN_SVUNIT_WITH_UVM +define+RUN_SVUNIT_WITH_UVM_REPORT_MOCK -P ${VCS_HOME}/include/hdl_xmr.tab +incdir+$UVM_HOME/src/vcs"
setenv ANALYZE_OBJECTS	"COMMON_LIB EASIER_UVM/tb tb_eugene"
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS "-ntb_opts uvm -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_MEDIUM +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait"
setenv EXIT_ON_ERROR	1
# a newline