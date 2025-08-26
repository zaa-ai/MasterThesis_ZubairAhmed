#################################################################################
# Write Out Final Design and Reports
#
#        .ddc:   Recommended binary format used for subsequent Design Compiler sessions
#    Milkyway:   Recommended binary format for IC Compiler
#        .v  :   Verilog netlist for ASCII flow (Formality, PrimeTime, VCS)
#       .spef:   Topographical mode parasitics for PrimeTime
#        .sdf:   SDF backannotated topographical mode timing for PrimeTime
#        .sdc:   SDC constraints for ASCII flow
#
#################################################################################

change_names -rules verilog -hierarchy

# ELMOS: rename all modules to prevent simulation overrides
rename_design -postfix "_nl" [remove_from_collection [get_designs *] $DESIGN_NAME]

# ELMOS: removed, not used here
#write_icc2_files -force  -output ${RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}

#Elmos: DS19-79 add command to remove unconnect ports
remove_unconnected_ports -blast [get_cell -hier] -blast_buses

#################################################################################
# Write out Design
#################################################################################

write -format verilog -hierarchy -output ${RESULTS_DIR}/${DCRM_FINAL_VERILOG_OUTPUT_FILE}

write -format ddc     -hierarchy -output ${RESULTS_DIR}/${DCRM_FINAL_DDC_OUTPUT_FILE}

# Write and close SVF file and make it available for immediate use
set_svf -off

#################################################################################
# Write out Design Data
#################################################################################

if {[shell_is_in_topographical_mode]} {

  # Note: A secondary floorplan file ${DCRM_DCT_FINAL_FLOORPLAN_OUTPUT_FILE}.objects
  #       might also be written to capture physical-only objects in the design.
  #       This file should be read in before reading the main floorplan file.

  write_floorplan -all ${RESULTS_DIR}/${DCRM_DCT_FINAL_FLOORPLAN_OUTPUT_FILE}

  # If the DCRM_DCT_SPG_PLACEMENT_OUTPUT_FILE variable has been set in dc_setup_filenames.tcl
  # file then the standard cell physical guidance is being created to support SPG ASCII hand-off
  # to IC Compiler by the write_def command.
  # Invoking write_def commands requires a Design Compiler Graphical license or an IC Compiler
  # Design Planning license.

  if {[info exists DCRM_DCT_SPG_PLACEMENT_OUTPUT_FILE]} {
    write_def -components -output ${RESULTS_DIR}/${DCRM_DCT_SPG_PLACEMENT_OUTPUT_FILE}
  }

  # Do not write out net RC info into SDC
  set_app_var write_sdc_output_lumped_net_capacitance false
  set_app_var write_sdc_output_net_resistance false

  set all_active_scenario_saved [all_active_scenarios]
  set current_scenario_saved [current_scenario]
  set_active_scenarios -all
  foreach scenario [all_active_scenarios] {
      current_scenario ${scenario}

    # Write parasitics data from Design Compiler Topographical placement for static timing analysis
    write_parasitics -output ${RESULTS_DIR}/[dcrm_mcmm_filename ${DCRM_DCT_FINAL_SPEF_OUTPUT_FILE} ${scenario}]

    # Write SDF backannotation data from Design Compiler Topographical placement for static timing analysis
    write_sdf ${RESULTS_DIR}/[dcrm_mcmm_filename ${DCRM_DCT_FINAL_SDF_OUTPUT_FILE} ${scenario}]

    write_sdc -nosplit ${RESULTS_DIR}/[dcrm_mcmm_filename ${DCRM_FINAL_SDC_OUTPUT_FILE} ${scenario}]
  }
  current_scenario ${current_scenario_saved}
  set_active_scenarios ${all_active_scenario_saved}
}

# If SAIF is used, write out SAIF name mapping file for PrimeTime-PX
 saif_map -type ptpx -write_map ${RESULTS_DIR}/${DESIGN_NAME}.mapped.SAIF.namemap

#################################################################################
# Generate Final Reports
#################################################################################

if { $OPTIMIZATION_FLOW  == "rtm_exp"} {
  set_host_options -max_cores 8
  update_timing

  parallel_execute [list \
  "report_qor > ${REPORTS_DIR}/${DCRM_FINAL_QOR_REPORT}" \
  "report_timing -transition_time -nets -attributes -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_TIMING_REPORT}" \
  "report_area -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_AREA_REPORT}" \
  "report_clock_gating -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_CLOCK_GATING_REPORT}" \
  ]

} else {
report_qor > ${REPORTS_DIR}/${DCRM_FINAL_QOR_REPORT}

report_timing -scenarios [all_active_scenarios] -transition_time -nets -attributes -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_TIMING_REPORT}

if {[shell_is_in_topographical_mode]} {
  #ELMOS: added option -hierarchy for a more detailed report https://jira.elmos.de/browse/DS19-278 
  report_area -hierarchy -physical -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_AREA_REPORT}
} else {
  report_area -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_AREA_REPORT}
}
report_area -designware  > ${REPORTS_DIR}/${DCRM_FINAL_DESIGNWARE_AREA_REPORT}
report_resources -hierarchy > ${REPORTS_DIR}/${DCRM_FINAL_RESOURCES_REPORT}
# ELMOS: added -ungated option, https://jira.elmos.de/browse/DS19-276
report_clock_gating -ungated -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_CLOCK_GATING_REPORT}
}

# Create a QoR snapshot of timing, physical, constraints, clock, power data, and routing on 
# active scenarios and stores it in the location  specified  by  the icc_snapshot_storage_location 
# variable. 

if {[shell_is_in_topographical_mode]} {
  set icc_snapshot_storage_location ${REPORTS_DIR}/${DCRM_DCT_FINAL_QOR_SNAPSHOT_FOLDER}
  create_qor_snapshot -name ${DCRM_DCT_FINAL_QOR_SNAPSHOT_REPORT} > ${REPORTS_DIR}/${DCRM_DCT_FINAL_QOR_SNAPSHOT_REPORT}
}


# Uncomment the next line to report all the multibit registers and the banking ratio in the design
# redirect ${REPORTS_DIR}/${DCRM_MULTIBIT_BANKING_REPORT} {report_multibit_banking -nosplit }

if { $OPTIMIZATION_FLOW == "hplp"} {
 redirect ${REPORTS_DIR}/${DCRM_MULTIBIT_BANKING_REPORT} {report_multibit_banking -nosplit }
}
# Use SAIF file for power analysis
# set current_scenario_saved [current_scenario]
# foreach scenario [all_active_scenarios] {
#   current_scenario ${scenario}
#   read_saif -auto_map_names -input ${DESIGN_NAME}.${scenario}.saif -instance < DESIGN_INSTANCE > -verbose
# }
# current_scenario ${current_scenario_saved}


report_power -scenarios [all_active_scenarios] -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_POWER_REPORT}
report_clock_gating -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_CLOCK_GATING_REPORT}

# Uncomment the next line if you include the -self_gating to the compile_ultra command
# to report the XOR Self Gating information.
# report_self_gating  -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_SELF_GATING_REPORT}

# Uncomment the next line to reports the number, area, and  percentage  of cells 
# for each threshold voltage group in the design.
# report_threshold_voltage_group -nosplit > ${REPORTS_DIR}/${DCRM_THRESHOLD_VOLTAGE_GROUP_REPORT}

if {[shell_is_in_topographical_mode]} {
  # report_congestion (topographical mode only) uses zroute for estimating and reporting 
  # routing related congestion which improves the congestion correlation with IC Compiler.
  # Design Compiler Topographical supports create_route_guide command to be consistent with IC
  # Compiler after topographical mode synthesis.
  # Those commands require a license for Design Compiler Graphical.

  report_congestion > ${REPORTS_DIR}/${DCRM_DCT_FINAL_CONGESTION_REPORT}

  # Use the following to generate and write out a congestion map from batch mode
  # This requires a GUI session to be temporarily opened and closed so a valid DISPLAY
  # must be set in your UNIX environment.

  # ELMOS: removed, not used here
  #if {[info exists env(DISPLAY)]} {
  #  gui_start
  #
  #  # Create a layout window
  #  set MyLayout [gui_create_window -type LayoutWindow]
  #
  #  # Build congestion map in case report_congestion was not previously run
  #  report_congestion -build_map
  #
  #  # Display congestion map in layout window
  #  gui_show_map -map "Global Route Congestion" -show true
  #
  #  # Zoom full to display complete floorplan
  #  gui_zoom -window [gui_get_current_window -view] -full
  #
  #  # Write the congestion map out to an image file
  #  # You can specify the output image type with -format png | xpm | jpg | bmp
  #
  #  # The following saves only the congestion map without the legends
  #  gui_write_window_image -format png -file ${REPORTS_DIR}/${DCRM_DCT_FINAL_CONGESTION_MAP_OUTPUT_FILE}
  #
  #  # The following saves the entire congestion map layout window with the legends
  #  gui_write_window_image -window ${MyLayout} -format png -file ${REPORTS_DIR}/${DCRM_DCT_FINAL_CONGESTION_MAP_WINDOW_OUTPUT_FILE}
  #
  #  gui_stop
  #} else {
  #  puts "Information: The DISPLAY environment variable is not set. Congestion map generation has been skipped."
  #}
}


#################################################################################
# Write out Milkyway Design for Top-Down Flow
#
# This should be the last step in the script
#################################################################################

if {[shell_is_in_topographical_mode]} {
  # write_milkyway uses mw_design_library variable from dc_setup.tcl
  write_milkyway -overwrite -output ${DCRM_FINAL_MW_CEL_NAME}
}

# ELMOS: removed, leave it to the main script if we want to exit the tool here
#exit
