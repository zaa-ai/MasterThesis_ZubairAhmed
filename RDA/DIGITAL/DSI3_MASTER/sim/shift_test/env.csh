setenv TESTBENCH testrunner
setenv TESTCASE  shift_test
setenv TC_DESCRIPTION "Unit test of DSI3 shift and sync module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_easier_uvm"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' -P ${VCS_HOME}/include/hdl_xmr.tab"
setenv ANALYZE_OBJECTS	"COMMON_LIB DSI3_MASTER DSI3_MASTER/tb/tb_shift"
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS "-debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
