setenv TESTBENCH testrunner
setenv TESTCASE  receiver_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Unit test of DSI3 receiver module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_eugene"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED +define+UVM_NO_VERDI_RECORD -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' -P ${VCS_HOME}/include/hdl_xmr.tab"
setenv ANALYZE_OBJECTS	"ECC DSI3_MASTER/tb/tb_dsi3_receiver tb_eugene "
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS "-ntb_opts uvm -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_MEDIUM +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait +uvm_set_type_override=dsi3_slave_driver,dsi3_slave_test_driver -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
