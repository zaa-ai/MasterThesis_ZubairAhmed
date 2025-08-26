source $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl
source $env(PROJECT_HOME)/scripts/misc/tcl/dc_suppress_trivial_messages.tcl

# Set the optimization flow to hplp (high performance low power)
set OPTIMIZATION_FLOW "hplp"
source -echo user_tcl/common_setup.tcl

source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup_filenames.tcl
source $env(PROJECT_HOME)/scripts/syn/tcl/dc/dc_setup.tcl;

read_ddc results/${DESIGN_NAME}.mapped.ddc
start_gui

