if { $OPTIMIZATION_FLOW == "rtm_exp"} {
# Dirty SDC constraints can increase runtime in both update_timing and compile_ultra commands. If update_timing takes longer than expected, you can identify the dirty SDC constraints using the check_timing -sdc_runtime command after loading a mapped netlist.
# check_timing -sdc_runtime
}
if {$OPTIMIZATION_FLOW != "rtm_exp"} {
#################################################################################
# Performing placement aware multibit banking
#################################################################################

#################################################################################
if {[shell_is_in_topographical_mode]} {
       # You can use placement aware multibit banking to group single-bit register cells that are
       # physically near each other into a multibit registers. 
       # This has to be done before DFT insertion in Design Compiler
       # These commands require a Design Compiler Graphical license
       # Please use -wns_threshold option with identify_register_banks command if u want to 
       # exclude specific percentage of timing critical registers from multibit banking
       # identify_register_banks -output ${RESULTS_DIR}/${DCRM_MULTIBIT_CREATE_REGISTER_BANK_FILE}
       # redirect ${REPORTS_DIR}/${DCRM_MULTIBIT_CREATE_REGISTER_BANK_REPORT} {source -echo -verbose ${RESULTS_DIR}/${DCRM_MULTIBIT_CREATE_REGISTER_BANK_FILE}}
}
#################################################################################


################################################################################
## RM+ Variable and Command Settings before incremental compile
################################################################################
if { $OPTIMIZATION_FLOW == "hplp" } {
    if {[shell_is_in_topographical_mode]} {
	# You can use placement aware multibit banking to group single-bit register cells that 
	# are physically near each other into a multibit registers
        # Please use -wns_threshold option with identify_register_banks command if u want to 
        # exclude specific percentage of timing critical registers from multibit banking
	identify_register_banks -output \
	    ${RESULTS_DIR}/${DCRM_MULTIBIT_CREATE_REGISTER_BANK_FILE}
	source -echo -verbose ${RESULTS_DIR}/${DCRM_MULTIBIT_CREATE_REGISTER_BANK_FILE}
    }
}
#################################################################################
# DFT Compiler Optimization Section
#################################################################################

    #############################################################################
    # Verilog Libraries for Test Design Rule Checking
    #############################################################################

    # For complex cells that do not have functional models in .lib format,
    # you can supply a list of TetraMAX-compatible Verilog libraries 
    # for test design rule checking.
    # Set the following variable in the dc_setup.tcl file:
    
    # set_app_var test_simulation_library <list of Verilog library files>

    #############################################################################
    # DFT Signal Type Definitions
    #
    # These are design-specific settings that should be modified.
    # The following are only examples and should not be used.
    #############################################################################

    # Define all global DFT signals in this section. If you define any Top-down DFT partitions, 
    # specify DFT signals in the DFT partitions section.
    # It is recommended that top-level test ports be defined as a part of the
    # RTL design and included in the netlist for floorplanning.

    # If you create test ports here and they are not in your floorplan, you should use
    # create_terminal for these additional test ports for topographical mode synthesis.

    if {[shell_is_in_topographical_mode]} {
      # create_terminal -layer "layer_name" -bounding_box {x1 y1 x2 y2} -port ScanPortName ... (repeat for each new test port)
    }

    # If you are using the internal pins flow, it is recommended to run the
    # change_names command before set_dft_signal to avoid problems after DFT insertion.
    # In this case, set_dft_signal pins should be based on pin names after change_names.
    #   -  Use the "-view existing_dft" for already connected DFT signals which must be 
    #      understood for the design to pass "dft_drc".
    #   -  Use the "-view spec" for DFT signals that DFT Compiler will use during
    #      "insert_dft" when making new scan connections.

    # change_names -rules verilog -hierarchy

    # set_dft_signal -view spec -type ScanDataOut -port SO
    # set_dft_signal -view spec -type ScanDataIn -port SI
    # set_dft_signal -view spec -type ScanEnable -port SCAN_ENABLE
    # set_dft_signal -view existing_dft -type ScanClock -port [list CLK] -timing {45 55}
    # set_dft_signal -view existing_dft -type Reset -port RESET -active 0

    puts "RM-Info: Sourcing script file [which ${DCRM_DFT_SIGNAL_SETUP_INPUT_FILE}]\n"
    source -echo -verbose ${DCRM_DFT_SIGNAL_SETUP_INPUT_FILE}
    
    #ELMOS: add remapping of non scan registers
    set_dft_insertion_configuration -unscan true
    
    #############################################################################
    # DFT for Clock Gating
    #
    # This section includes variables and commands used only when clock gating
    # has been performed in the design.
    #############################################################################

    # Use the following command to initialize clock gating cells for test that are
    # made transparent with a signal held constant for testing, e.g. of type 'Constant'.
    # The value set depends on the hierarchy depth of the clock-gating cells.
    # This setting is not needed where clock-gating cells are controlled with scan enable.

    # set_dft_drc_configuration -clock_gating_init_cycles 1

    # To specify a dedicated ScanEnable/TestMode signal to be used for clock gating,
    # use the "-usage clock_gating" option of the "set_dft_signal" command

    # set_dft_signal -view spec -type <ScanEnable|TestMode> -port <dedicated port> -usage clock_gating

    # You can specify the clock-gating connectivity of the ScanEnable/TestMode signals
    # after they are predefined with set_dft_signal -usage clock_gating

    # set_dft_connect <LABEL> -type clock_gating_control -source <DFT signal> [-target ...]

    #############################################################################
    # DFT Configuration
    #############################################################################

    # Preserve the design name when writing to the database during DFT insertion. 
    set_dft_insertion_configuration -preserve_design_name true

    # Do not perform synthesis optimization during DFT insertion. 
    set_dft_insertion_configuration -synthesis_optimization none

    # Multibit cell handling
    # Specify -preserve_multibit_segment to false to treat the cells inside a
    # multibit component as discrete sequential cells. This improves balancing
    # of scan chains.
    # Starting I-2013.12 release, the default setting is false
    # set_scan_configuration -preserve_multibit_segment false

# ELMOS: clock mixing to be defined in ${DCRM_DFT_SIGNAL_SETUP_INPUT_FILE}

    ## DFT Clock Mixing Specification
    # For a hierarchical flow, don't mix clocks at the block level:
    # set_scan_configuration -clock_mixing no_mix

    # For a top-down methodology clock mixing is recommended, if possible:
    #set_scan_configuration -clock_mixing mix_clocks

    #############################################################################
    # DFT AutoFix Configuration
    #############################################################################

    # Please refer to the TestMAX DFT User Guide, Chapter 12,
    # "Advanced DFT Architecture Methodologies", "Using AutoFix" section.

    # Please refer to the dc.dft_autofix_config.tcl file included with the
    # Design Compiler Reference Methodology scripts for an example of a
    # design-specific AutoFix configuration.

    # Create a design-specific Autofix configuration file and uncomment the
    # following line to source this file.

    # source -echo -verbose ${DCRM_DFT_AUTOFIX_CONFIG_INPUT_FILE}

}
