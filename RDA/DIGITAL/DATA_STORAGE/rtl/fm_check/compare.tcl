set DESIGN_NAME                   "buffer"  ;#  The name of the top-level design

#################################################################################
# Formality Flow Files
#################################################################################

set REPORTS_DIR "reports"
set RESULTS_DIR "results"

set DCRM_SVF_OUTPUT_FILE                                ${DESIGN_NAME}.mapped.svf

set FMRM_UNMATCHED_POINTS_REPORT                        ${DESIGN_NAME}.fmv_unmatched_points.rpt

set FMRM_FAILING_SESSION_NAME                           ${DESIGN_NAME}
set FMRM_FAILING_POINTS_REPORT                          ${DESIGN_NAME}.fmv_failing_points.rpt
set FMRM_ABORTED_POINTS_REPORT                          ${DESIGN_NAME}.fmv_aborted_points.rpt
set FMRM_ANALYZE_POINTS_REPORT                          ${DESIGN_NAME}.fmv_analyze_points.rpt


source $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl
set TECH $env(PROJECT_HOME)/tech/TSMC_180_BCD

#source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup_filenames.tcl
#source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup.tcl

set_app_var synopsys_auto_setup true

set old_search_path $search_path
# New search_path obtained by autoread analysis.
set search_path [list . /nfs/wrk.jvoi/projekte/52143/p52143/ANALOG/../DIGITAL/be_run/syn/def /nfs/wrk.jvoi/projekte/52143/p52143/ANALOG/../DIGITAL/config /nfs/wrk.jvoi/projekte/52143/p52143/ANALOG/../DIGITAL/edf_registers /nfs/wrk.jvoi/projekte/52143/p52143/ANALOG/../DIGITAL/rtl /nfs/wrk.jvoi/projekte/52143/p52143/ANALOG/../DIGITAL/DATA_STORAGE/rtl . /common/run/synopsys/designcompiler/P-2019.03-SP5-6/libraries/syn /common/run/synopsys/designcompiler/P-2019.03-SP5-6/dw/syn_ver /common/run/synopsys/designcompiler/P-2019.03-SP5-6/dw/sim_ver user_tcl def sdc /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/tech/TSMC_180_BCD/hdl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/MAIN_CONTROL /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/SPI /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/TIMEBASE /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/DSI3_MASTER /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/COMMON_LIB /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/TEST /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/ECC /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/DATA_STORAGE /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/OTP_MEM /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/COMMON_LIB/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/DSI3_MASTER/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/ECC/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/MAIN_CONTROL/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/OTP_MEM/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/SPI/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/UTILS_LIB /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/ECC_LIB /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/RAM_ROM_LIB /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/inc /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/ECC_LIB/hdl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/ECC_LIB/doc /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/RAM_ROM_LIB/hdl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/UTILS_LIB/hdl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/STD_COMPONENTS/UTILS_LIB/doc /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/TEST/rtl /nfs/wrk.jvoi/projekte/52143/p52143/DIGITAL/TIMEBASE/rtl ]

read_sverilog -r -libname WORK { ../../../rtl/project_pkg.sv }
read_sverilog -r -libname WORK { ../buffer_if_pkg.sv }
read_sverilog -r -libname WORK { ../../../COMMON_LIB/rtl/clk_reset_if.sv }
read_sverilog -r -libname WORK { ../buffer_reader_if.sv }
read_sverilog -r -libname WORK { ../buffer_writer_if.sv }
read_sverilog -r -libname WORK { ../../../rtl/elip_full_if.sv }
read_sverilog -r -libname WORK { ../../.././COMMON_LIB/rtl/elip_if.sv }
read_sverilog -r -libname WORK { ../../.././ECC/rtl/ecc_error_if.sv }
read_sverilog -r -libname WORK { ../../../edf_registers/ring_buffer_registers.sv }
read_sverilog -r -libname WORK { buffer.r2189.sv }
set_top r:/WORK/${DESIGN_NAME}

read_sverilog -i -libname WORK { ../../../rtl/project_pkg.sv }
read_sverilog -i -libname WORK { ../buffer_if_pkg.sv }
read_sverilog -i -libname WORK { ../../../COMMON_LIB/rtl/clk_reset_if.sv }
read_sverilog -i -libname WORK { ../buffer_reader_if.sv }
read_sverilog -i -libname WORK { ../buffer_writer_if.sv }
read_sverilog -i -libname WORK { ../../../rtl/elip_full_if.sv }
read_sverilog -i -libname WORK { ../../.././COMMON_LIB/rtl/elip_if.sv }
read_sverilog -i -libname WORK { ../../.././ECC/rtl/ecc_error_if.sv }
read_sverilog -i -libname WORK { ../../../edf_registers/ring_buffer_registers.sv }
read_sverilog -i -libname WORK { ../buffer.sv }
set_top i:/WORK/${DESIGN_NAME}

set search_path $old_search_path

set_app_var svf_port_constant false
set_app_var verification_timeout_limit "0:30:0"
set_app_var verification_clock_gate_edge_analysis true
set_app_var verification_clock_gate_hold_mode any
set_app_var verification_failing_point_limit 0

set_app_var hdlin_unresolved_modules black_box

set verification_progress_report_interval 5

#################################################################################
# Match compare points and report unmatched points 
#################################################################################
match
report_unmatched_points


#################################################################################
# Verify and Report
#
# If the verification is not successful, the session will be saved and reports
# will be generated to help debug the failed or inconclusive verification.
#################################################################################


if { ![verify] }  {  
  save_session -replace ${REPORTS_DIR}/${FMRM_FAILING_SESSION_NAME}
  report_failing_points > ${REPORTS_DIR}/${FMRM_FAILING_POINTS_REPORT}
  report_aborted > ${REPORTS_DIR}/${FMRM_ABORTED_POINTS_REPORT}
  # Use analyze_points to help determine the next step in resolving verification
  # issues. It runs heuristic analysis to determine if there are potential causes
  # other than logical differences for failing or hard verification points. 
  analyze_points -all > ${REPORTS_DIR}/${FMRM_ANALYZE_POINTS_REPORT}
}

exit
