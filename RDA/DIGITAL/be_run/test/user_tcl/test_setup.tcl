puts "-------------------------------------------------------------------------------"
puts "RM-Info: Running script [info script]"
puts "-------------------------------------------------------------------------------"
#return -level 3

set TECH [exec getPrjCfg.rb -p tech]

##################################################################
#    RUNTIME: Set runtime variables                              #
##################################################################

# Change TMAX_DEBUG_MODE to TRUE to print a more complete log file and
# additional reports for debugging (e.g lockup latch violations).
set TMAX_DEBUG_MODE TRUE

# Change TMAX_COMPRESSION_MODE to FALSE to run DRC and ATPG for Internal_scan
# mode instead of ScanCompression_mode. This allows achieved compression
# to be calculated.
set TMAX_COMPRESSION_MODE TRUE

# If WITH_WRAPPER is set to anything the Flow runs on a wrapped design..
# Leave blank ("") when running on design netlist...
set WITH_WRAPPER ""
if {$env(WRAPPER) ne ""} {
set WITH_WRAPPER "TRUE"
}

##################################################################
#    DIRECTORIES: Set up output directories                      #
##################################################################

if {$WITH_WRAPPER == ""} {
    set DESIGN_NAME "digtop"  ;#  The name of the top-level design
    set TB_NAME     "digtop_tb"  ;#  The name of the top-level testbench
} else {
    set DESIGN_NAME "asic_shell"  ;#  The name of the wrapper
    set TB_NAME     "digtop_tb"  ;#  The name of the top-level testbench
}

puts "RM-Info: DESIGN_NAME variable is set to ${DESIGN_NAME}\n"
puts "RM-Info: TB_NAME variable is set to ${TB_NAME}\n"

set REPORTS_DIR "reports"
set RESULTS_DIR "results"
file mkdir $REPORTS_DIR
file mkdir $RESULTS_DIR

##################################################################
# Define Scan and Reset Ports
##################################################################
#set TEST_MODE    [exec getPrjCfg.rb config/test/test_mode] ;#not needed anymore
set SCAN_RES     [exec getPrjCfg.rb config/test/scan_res]
set SCAN_CLK     [exec getPrjCfg.rb config/test/scan_clk]
set SCAN_SCK     [exec getPrjCfg.rb config/test/scan_sck]
set SCAN_ENABLE  [exec getPrjCfg.rb config/test/scan_enable]
set SCAN_DIN1    [exec getPrjCfg.rb config/test/scan_din1]
set SCAN_DOUT1   [exec getPrjCfg.rb config/test/scan_dout1]
set SCAN_DIN2    [exec getPrjCfg.rb config/test/scan_din2]
set SCAN_DOUT2   [exec getPrjCfg.rb config/test/scan_dout2]
set SCAN_DIN3    [exec getPrjCfg.rb config/test/scan_din3]
set SCAN_DOUT3   [exec getPrjCfg.rb config/test/scan_dout3]

if {$WITH_WRAPPER != ""} {
# Using T2000 pin names
set SCAN_RES     "RESB__MDMA_DPIN"
set SCAN_CLK     "BFWB_TCK__MDMA_DPIN"
set SCAN_ENABLE  "RFC__MDMA_DPIN"
set SCAN_DIN1    "MOSI__MDMA_DPIN"
set SCAN_DOUT1   "MISO__MDMA_DPIN"
set SCAN_DIN2    "DAB_TMS__MDMA_DPIN"
set SCAN_DOUT2   "INTB_TDO__MDMA_DPIN"
set SCAN_DIN3    "CSB__MDMA_DPIN"
set SCAN_DOUT3   "SYNCB_TDI__MDMA_DPIN"
set SCAN_SCK	 "SCK__MDMA_DPIN"
}

##################################################################
#    SETUP: Variables for overall execution                      #
##################################################################

## ELMOS: added default capture cycles
set CAPTURE_CYCLES          "4"

set RULES_TO_DOWNGRADE      "" ;# errors to downgrade without masking (default: none)
set RULES_TO_MASK           "" ;# errors to downgrade with masking (default: none)

##################################################################
#    BUILD: Variables for reading in and building the design     #
##################################################################

# Modules to replace by black boxes (default: none)
set MODULES_TO_BLACK_BOX     "otp4kx12_cp_nl"
append $MODULES_TO_BLACK_BOX "ips_tsmc180bcd50_p1r_ad"
append $MODULES_TO_BLACK_BOX "slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20"
append $MODULES_TO_BLACK_BOX "tmode"

set INSTANCES_TO_BLACK_BOX  "" ;# Instances to replace by TIEX's (default: none)
set TMAX_LIBRARY_FILES      "[exec getPrjCfg.rb -r $TECH -p tech/models/fault]" ;# Cell libraries, nofaulted inside modules (REQUIRED)
set NETLIST_FILES           "../layout/results/digtop.output.v " ;# Design files, faulted inside modules (default: DC-RM output)
if {$WITH_WRAPPER != ""} {
    append NETLIST_FILES        "./hdl/asic.v "
    append NETLIST_FILES        "./hdl/asic_shell.v "
}
## ELMOS: Define Name of Files that contains a list of in- and output signals
##        that are to be removed from NETLIST and PROTOCOL File:
##          -NETLIST Patch : done within "test_build_setup.tcl"
##          -PROTOCOL Patch: done within "test_td_drc.tcl" and "test_sa_drc.tcl"

if {$WITH_WRAPPER != ""} {
    set NONDFT_IN_SIGNAL_FILE   ""
    set NONDFT_OUT_SIGNAL_FILE  ""
} else {
    set NONDFT_IN_SIGNAL_FILE   "../syn/results/nonDFT_in_signals_file.txt"
    set NONDFT_OUT_SIGNAL_FILE  "../syn/results/nonDFT_out_signals_file.txt"
}
##################################################################
#    DRC: Files used by DRC for all ATPG runs.                   #
##################################################################

# NOTE: Only one PROTOCOL_FILE name may be specified per TetraMAX run.

if {$WITH_WRAPPER != ""} {

    if { $TMAX_COMPRESSION_MODE } {
	set PROTOCOL_FILE        "./stil/digtop.mapped.scancompress.spf_ATE_pins" ;# ScanCompression_mode STIL Protocol File (default: DC-RM output)
    } else {
	set PROTOCOL_FILE        "./stil/digtop.mapped.iddq.spf_ATE_pins" ;# Internal_scan mode STIL Protocol File (default: DC-RM output)
    }

} else {

    if { $TMAX_COMPRESSION_MODE } {
	set PROTOCOL_FILE        "../syn/results/digtop.mapped.scancompress.spf" ;# ScanCompression_mode STIL Protocol File (default: DC-RM output)
    } else {
	set PROTOCOL_FILE        "../syn/results/digtop.atpg_std_init.ctl" ;# Internal_scan mode STIL Protocol File (default: DC-RM output)
    }
}
set EXCEPTION_FILES         "" ;# SDC files for timing exceptions (default: PT-RM output)

## ELMOS: define the fast waveform table names as used in Test Protocol File
#         -> required only to write constraints for PrimeTime. Use a blank space
#            to separate multiple entries or leave empty if not used
set WFT_TD_DRC              ""; # (default: DC-RM output "_allclock_launch_WFT_ _allclock_capture_WFT_"

##################################################################
#    SPECIAL: Files used by special ATPG runs.                   #
##################################################################

# NOTE: Only one GLOBAL_SLACK_FILE name may be specified per TetraMAX run.
if {$WITH_WRAPPER != ""} {
set GLOBAL_SLACK_FILE       "./slack.file" ;# adapted Slack File with additional hierachy of wrapper for Slack-Based Transition Fault Testing. Created with 'make slack.file' or 'make spf'
} else {
set GLOBAL_SLACK_FILE       "../signoff/reports/digtop_func_max_report_global_slack.report" ;# Slack File for Slack-Based Transition Fault Testing (default: PT-RM output)
}
set MAX_TMGN                "5" ;## ELMOS: SLACK parameter (default: 30%)
set MAX_DELTA_PER_FAULT     "" ;## ELMOS: SLACK parameter (default: 0)

# NOTE: Only one NODE_FILE name may be specified per TetraMAX run.
if {$WITH_WRAPPER != ""} {
 set NODE_FILE               "./bridge.file" ;# adapted node file with additional hierarchy of wrapper for bridging faults (REQUIRED). Created with 'make bridge.file' or 'make spf'
} else {
 set NODE_FILE               "../signoff/results/bridge.file" ;# Node file for bridging faults (REQUIRED)
}

## ELMOS: Fault Model for Cell Aware Test (example: <techlib>/tmax/ctm/*.ctm)
set CELL_MODEL              "$TECH/TCB018GBWP7T/tmax/ctm/*.ctm"

## ELMOS: Variable to define special command options for writing WGL/BIN/STIL Patterns (Optional)
set WGL_OPT                 "-exclude setup -use_delay_capture_start 1 -use_delay_capture_end 1"
set BIN_OPT                 ""
set STIL_OPT                ""

##################################################################
# ELMOS: Required Variables for each fault model!!!              #
##################################################################
#
#  Fault Models:
#   DB: Dynamic Bridging
#   CT: Cell Aware Transition
#   TD: Transition Delay
#   SB: Static Bridging
#   SA: Stuck-At
#   CA: Cell Aware Stuck-At
#   ID: IDDQ
#
# coverage limits
set COVERAGE_DB_ATPG        "100"
set COVERAGE_TD_ATPG        "100"
set COVERAGE_TD_SLACK_ATPG  "100"
set COVERAGE_CT_ATPG        "100"
set COVERAGE_CT_SLACK_ATPG  "100"
set COVERAGE_SB_ATPG        "100"
set COVERAGE_SA_ATPG        "100"
set COVERAGE_CS_ATPG        "100"
set COVERAGE_ID_ATPG        "100"

# abort limits (TetraMAX II: not used, leave default value "10")
# -> use a blank space to separate multiple runs with different limits
set LIMIT_DB_ATPG           "10"
set LIMIT_TD_ATPG           "10"
set LIMIT_TD_SLACK_ATPG     "10"
set LIMIT_CT_ATPG           "10"
set LIMIT_CT_SLACK_ATPG     "10"
set LIMIT_SB_ATPG           "10"
set LIMIT_SA_ATPG           "10"
set LIMIT_CS_ATPG           "10"
set LIMIT_ID_ATPG           "10"

# custom fault scripts
# use a custom fault script to define faults other than "add_faults -all")
set CUSTOM_DB_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_TD_SLACK_ADD_FAULTS_SCRIPT "user_tcl/tmax_faults.tcl"
set CUSTOM_TD_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_CT_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_CT_SLACK_ADD_FAULTS_SCRIPT "user_tcl/tmax_faults.tcl"
set CUSTOM_SB_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_SA_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_CS_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"
set CUSTOM_ID_ADD_FAULTS_SCRIPT       "user_tcl/tmax_faults.tcl"


# custom constraint script
# use a custom constraint script to define the state on the Primary Inputs (top-level inputs)
set CUSTOM_TD_CONSTRAINTS_SCRIPT "user_tcl/test_td_constraints.tcl"
set CUSTOM_SA_CONSTRAINTS_SCRIPT ""

# Hierarchical Fault Reporting
set HIER_LEVEL "" ;# depth of hierarchical reporting (default: 5)
set MIN_FAULTS "" ;# minimum number of faults per block (default: 32)

puts "-------------------------------------------------------------------------------"
puts "RM-Info: Completed script [info script]"
puts "-------------------------------------------------------------------------------"
