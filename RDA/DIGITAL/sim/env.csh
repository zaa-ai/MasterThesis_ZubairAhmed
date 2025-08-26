setenv TESTBENCH top_tb
setenv TESTCASE  standard
setenv TC_DESCRIPTION "standard environment (do not use!)"  
setenv GENERATE_OPTIONS
setenv GENERATE_OBJECTS "generate_eugene"
setenv ANALYZE_OPTIONS "-sverilog +define+INITIALIZE_MEMORY +define+UVM_NO_DEPRECATED +define+UVM_NO_VERDI_RECORD -timescale=1ns/1ps +define+PATTERN_FILE_LOCATION='$DESIGN/verification/pattern/'"
setenv ANALYZE_OBJECTS	"tech/TSMC_180_BCD STD_COMPONENTS COMMON_LIB ECC otp OTP_MEM DATA_STORAGE MAIN_CONTROL DSI3_MASTER TIMEBASE SPI edf_registers TEST rtl model tb_eugene"
setenv LINT_OPTIONS "+lint=all,noSVA-NSVU,noZERO,noSVA-UA,noSVA-AECASR,noSVA-DIU,noPORTFRC,noSVA-CE,noSVA-ICP"
setenv VCS_COVERAGE_OPTIONS "-cm_noconst -cm line+cond+fsm+tgl+branch+assert -cm_tgl mda -cm_line contassign"
setenv DEBUG_OPTIONS "-debug_access+all+reverse -debug_region+cell"
setenv ELAB_OPTIONS "+vcs+lic+wait -notice -debug_report  -xlrm floating_pnt_constraint -Xrerolloff"
setenv VCS_OPTIONS "-l simv.log +UVM_VERBOSITY=UVM_MEDIUM +bus_conflict_off +warn=noFCICIO -ucli -assert nopostproc +UVM_LOG_RECORD -verdi_opts '-ssr Verdi.ses'"
setenv EXIT_ON_ERROR	1
setenv USERS "jvoi,mkue,tle,boli,jvos"
setenv DEFAULT_PARSER uvm_simulation.parser
# do not forget the newline at the end

