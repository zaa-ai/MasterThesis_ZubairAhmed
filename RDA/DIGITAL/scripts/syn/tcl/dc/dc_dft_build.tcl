if {$OPTIMIZATION_FLOW != "rtm_exp"} {
#################################################################################
# Performing placement aware multibit banking
#################################################################################

    ###########################################################################
    # Defining DFT partitions
    ###########################################################################
    # Use the define_dft_partition command to define a set of clock domains, design references,
    # hierarchical cells, or sequential leaf cells that you can specify scan and compression configuration.
    # Then use the current_dft_partition command to set the current partition, then apply one or more
    # supported test configuration commands to configure scan for that partition.
    # Define any partition specific DFT signals in this section.
    #
    # Be sure to define any global scan and compression configuration and signals before define_dft_partition command.
    #
    # Please refer to the TestMAX DFT User Guide, Chapter 18,
    # "Using DFTMAX Compression", "Top-Down Flat Compressed Scan Flow with Partitions" section.
    #
    # define_dft_partition <partition_1>       \
    #   -include <list_of_cells_or_references> \
    #   -clocks  <list of_clocks>
    #
    # define_dft_partition <partition_2>       \
    #   -include <list_of_cells_or_references> \
    #   -clocks  <list of_clocks>
    #
    # current_dft_partition <partition_1>
    # <Scan and Compression configuration for partition_1>
    # If you have defined multiple test modes, you must use -test_mode option when defining DFT signals.
    # <DFT signals specific to partition_1>
    #
    # current_dft_partition <partition_2>
    # <Scan and Compression configuration for partition_2>
    # If you have defined multiple test modes, you must use -test_mode option when defining DFT signals.
    # <DFT signals specific to partition_2>
    
    #############################################################################
    # DFT Test Protocol Creation
    #############################################################################

    create_test_protocol

    #############################################################################
    # DFT Insertion
    #############################################################################

    # Use the -verbose version of dft_drc to assist in debugging if necessary

    streaming_dft_planner                      > ${REPORTS_DIR}/streaming_dft_planner.report
    
    dft_drc
    # ELMOS: creating report file only for debugging
    if {$env(DEBUG) eq 1} {                                
    dft_drc -verbose                           > ${REPORTS_DIR}/${DCRM_DFT_DRC_CONFIGURED_VERBOSE_REPORT}
	}
    report_scan_configuration                  > ${REPORTS_DIR}/${DCRM_DFT_SCAN_CONFIGURATION_REPORT}
    report_scan_compression_configuration      > ${REPORTS_DIR}/${DCRM_DFT_COMPRESSION_CONFIGURATION_REPORT}
    report_streaming_compression_configuration > ${REPORTS_DIR}/${DESIGN_NAME}.streaming_compression_configuration.rpt
    report_dft_insertion_configuration         > ${REPORTS_DIR}/${DCRM_DFT_PREVIEW_CONFIGURATION_REPORT}

    # Use the -show all version to preview_dft for more detailed report
    preview_dft                                > ${REPORTS_DIR}/${DCRM_DFT_PREVIEW_DFT_SUMMARY_REPORT}
    preview_dft -show all -test_points all     > ${REPORTS_DIR}/${DCRM_DFT_PREVIEW_DFT_ALL_REPORT}

    insert_dft

    #################################################################################
    # Re-create Default Path Groups
    #
    # In case of ports being created during insert_dft they need to be added
    # to those path groups.
    # Separating these paths can help improve optimization.
    #################################################################################
    
    set current_scenario_saved [current_scenario]
    foreach scenario [all_active_scenarios] {
      current_scenario ${scenario}
      set ports_clock_root [filter_collection [get_attribute [get_clocks] sources] object_class==port]
      group_path -name REGOUT -to [all_outputs]
      group_path -name REGIN -from [remove_from_collection [all_inputs] ${ports_clock_root}]
      group_path -name FEEDTHROUGH -from [remove_from_collection [all_inputs] ${ports_clock_root}] -to [all_outputs]
    }
    current_scenario ${current_scenario_saved}
}
