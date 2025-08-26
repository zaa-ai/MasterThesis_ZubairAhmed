setenv TESTBENCH testrunner
setenv TESTCASE  spi_core_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Unit test of SPI core module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_easier_uvm"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' -P ${VCS_HOME}/include/hdl_xmr.tab"
setenv ANALYZE_OBJECTS	"COMMON_LIB ECC SPI/tb/tb_spi_core tb_easier_uvm "
setenv DEBUG_OPTIONS " -debug_access+all -debug_region+cell"
setenv ELAB_OPTIONS "-ntb_opts uvm -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_MEDIUM +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
