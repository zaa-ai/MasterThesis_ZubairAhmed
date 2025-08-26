
source user_tcl/common_setup.tcl

# fix for missing TECH directory definition (module_config.xml?)
set TECH $env(PROJECT_HOME)/tech/TSMC_180_BCD

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup_filenames.tcl
source -echo $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup.tcl

set_app_var synopsys_auto_setup_filter {scan_input}

source -echo $env(PROJECT_HOME)/scripts/syn/tcl/fm/fm_settings.tcl

set_app_var svf_port_constant false
set_app_var verification_timeout_limit "0:30:0"
set_app_var verification_clock_gate_edge_analysis true

#set_app_var verification_clock_gate_hold_mode any
set_app_var verification_clock_gate_reverse_gating true

set_app_var verification_failing_point_limit 0

set_app_var hdlin_unresolved_modules black_box

set_host_options -max_cores 4
set verification_progress_report_interval 5

#################################################################################
# Configure constant ports
#
# When using the Synopsys Auto Setup mode, the SVF file will convey information
# automatically to Formality about how to disable scan.
#
# Otherwise, manually define those ports whose inputs should be assumed constant
# during verification.
#
# Example command format:
#
#   set_constant -type port i:/WORK/${DESIGN_NAME}/<port_name> <constant_value> 
#
#################################################################################
set_constant -type cell r:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers/i_scan_registers_SCAN/SCAN_reg 0
set_constant -type cell r:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers/i_scan_registers_SCAN/COMPRESSION_reg 0
set_constant -type cell r:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers/i_scan_registers_SCAN/VDD_DIS_reg 0

set_constant -type cell i:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers_i_scan_registers_SCAN_SCAN_reg 0
set_constant -type cell i:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers_i_scan_registers_SCAN_COMPRESSION_reg 0
set_constant -type cell i:/WORK/${DESIGN_NAME}/i_logic_top/i_test/i_test_control/i_scan_registers_i_scan_registers_SCAN_VDD_DIS_reg 0

source $env(PROJECT_HOME)/scripts/syn/tcl/fm/fm_match.tcl

puts "RM-Info: Completed script [info script]\n"
print_message_info

if {$env(QUIT) != 0} {
  exit
}

