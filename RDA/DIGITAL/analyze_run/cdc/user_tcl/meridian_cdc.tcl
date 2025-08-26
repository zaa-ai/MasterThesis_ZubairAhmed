#------------------------------------------------------------------------------
# Common Setup Section
#------------------------------------------------------------------------------
set INPUT_DRIVER 		$env(INPUT_DRIVER)
source                          $env(PROJECT_HOME)/be_run/syn/sdc/$env(TOP_MODULE).constraints.procs.tcl
set MERIDIAN_SDC_INPUT          $env(PROJECT_HOME)/be_run/syn/sdc/$env(TOP_MODULE).constraints.$env(SDC).tcl
set MERIDIAN_SDC2ENV_OUTPUT     ./results/$env(TOP_MODULE).sdc2env.$env(SDC).env

set MERIDIAN_CONSTRAINT_INPUT   ./user_tcl/$env(TOP_MODULE).constraints.$env(SCENARIO).env
set MERIDIAN_WAIVER_INPUT       ./waiver/$env(TOP_MODULE).waiver.$env(SCENARIO).tcl

set MERIDIAN_CONSOLIDATE_OUTPUT ./results/$env(TOP_MODULE).consolidated.$env(SCENARIO).env
set MERIDIAN_POLICY_REPORT      ./reports/$env(TOP_MODULE).policy.$env(SCENARIO).rpt

#------------------------------------------------------------------------------
# Data Import Section
#------------------------------------------------------------------------------

foreach lib [ list $env(GATES_LIB) ] {
   read_liberty ${lib}
}

foreach rtl [ list $env(SOURCE_LIST) ] {
   analyze -f ${rtl} -ignore_translate_off synopsys
}

analyze ../../rtl/DIGITAL_TECH_pkg.vhd -work DIGITAL
analyze ../../rtl/DIGITAL_pkg.vhd -work DIGITAL
analyze ../..//TEST/rtl/jtag_tap_pkg.vhd -work JTAG
analyze -f ../../config/otp_mem_vhdl_pkg.f -work OTP_MEM
analyze -f ../../config/otp_mem_vhdl.f -work OTP_MEM

elaborate $env(TOP_MODULE) -auto_black_box

#------------------------------------------------------------------------------
# Tool Setup Section
#------------------------------------------------------------------------------
# put here any settings for tool-variables that are non default:


#------------------------------------------------------------------------------
# Constraint Import Section
#------------------------------------------------------------------------------

# Read and convert the SDC to ENV
#
create_scenario sdc
current_scenario sdc

if [file exists ${MERIDIAN_SDC_INPUT}] {
    read_sdc ${MERIDIAN_SDC_INPUT} -output_env ${MERIDIAN_SDC2ENV_OUTPUT}
} else {
    puts "Error: Cannot find user SDC constraint file ${MERIDIAN_SDC_INPUT}"
    exit 1
}

read_sdc ./user_tcl/additional_sdc_commands.tcl

# Read converted and user constraints
#
create_scenario env
current_scenario env

read_env ${MERIDIAN_SDC2ENV_OUTPUT}

if [file exists ${MERIDIAN_CONSTRAINT_INPUT}] {
    read_env ${MERIDIAN_CONSTRAINT_INPUT}
} else {
    puts "Error: Cannot find user constraint file ${MERIDIAN_CONSTRAINT_INPUT}"
    exit 1
}

#------------------------------------------------------------------------------
# Run Setup and CDC Check
#------------------------------------------------------------------------------

analyze_intent -disable_auto_intent_generation -output_env ${MERIDIAN_CONSOLIDATE_OUTPUT} 
verify_cdc 

#------------------------------------------------------------------------------
# Apply Waiver File
#------------------------------------------------------------------------------

if [file exists ${MERIDIAN_WAIVER_INPUT}] {
    source ${MERIDIAN_WAIVER_INPUT}
} else {
    puts "Error: Cannot find user waiver file ${MERIDIAN_WAIVER_INPUT}"
    exit 1
}

#------------------------------------------------------------------------------
# Final OUTPUT
#------------------------------------------------------------------------------

report_policy {ALL} -verbose -compat -out ${MERIDIAN_POLICY_REPORT}

