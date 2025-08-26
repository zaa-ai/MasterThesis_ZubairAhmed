setenv TESTBENCH testrunner
setenv TESTCASE  ecc_register_test
setenv TC_DESCRIPTION "Unit test of generic ecc register module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS ""
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' +define+HAVE_PG_PINS"
setenv ANALYZE_OBJECTS	"ECC ECC/tb/tb_ecc_register "
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS " -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait"
setenv EXIT_ON_ERROR	1
