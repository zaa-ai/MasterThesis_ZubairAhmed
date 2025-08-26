setenv TESTBENCH testrunner
setenv TESTCASE  spi_test
setenv UVM_TESTCASE top_test
setenv TC_DESCRIPTION "Unit test of SPI module"
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_eugene"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv ANALYZE_OPTIONS "-sverilog +define+UVM_NO_DEPRECATED -timescale=1ps/1ps +define+SVUNIT_VERSION='3_26' -P ${VCS_HOME}/include/hdl_xmr.tab +define+UVM_NO_VERDI_RECORD"
setenv ANALYZE_OBJECTS	"COMMON_LIB edf_registers STD_COMPONENTS DATA_STORAGE ECC SPI tb_eugene SPI/tb/tb_spi"
setenv DEBUG_OPTIONS " -debug_access+all+reverse -debug_region+cell"
setenv ELAB_OPTIONS "-ntb_opts uvm -debug_report -notice"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_LOW +warn=noFCICIO -ucli -assert nopostproc +vcs+lic+wait -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
