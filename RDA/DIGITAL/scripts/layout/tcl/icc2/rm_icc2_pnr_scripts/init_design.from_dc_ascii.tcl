##########################################################################################
# Script: init_design.from_dc_ascii.tcl
# Version: S-2021.06
# Copyright (C) 2014-2021 Synopsys, Inc. All rights reserved.
##########################################################################################

########################################################################
## Library creation
########################################################################

	if {[file exists $DESIGN_LIBRARY]} {
		file delete -force $DESIGN_LIBRARY
	}
	
	set create_lib_cmd "create_lib $DESIGN_LIBRARY"

	if {[file exists [which $TECH_FILE]]} {
		lappend create_lib_cmd -tech $TECH_FILE ;# recommended
	} elseif {$TECH_LIB != ""} {
		lappend create_lib_cmd -use_technology_lib $TECH_LIB ;# optional
	}

	if {$DESIGN_LIBRARY_SCALE_FACTOR != ""} {
		lappend create_lib_cmd -scale_factor $DESIGN_LIBRARY_SCALE_FACTOR
	}

	set_app_options -name lib.setting.on_disk_operation -value true ;# default false and global-scoped

	## Library configuration flow: calls library manager under the hood to generate .nlibs, store, and link them
	#  - To enable it, in icc2_common_setup.tcl, set LIBRARY_CONFIGURATION_FLOW to true,
	#    specify LINK_LIBRARY with .db files, and specify REFERENCE_LIBRARY with physical source files. 
	#    In icc2_pnr_setup.tcl, make sure search_path includes all relevant locations. 
	if {$LIBRARY_CONFIGURATION_FLOW} {
		set link_library $LINK_LIBRARY
	}

	lappend create_lib_cmd -ref_libs $REFERENCE_LIBRARY

	puts "RM-info: $create_lib_cmd"
	eval ${create_lib_cmd}

########################################################################
## Design creation
########################################################################

	################################################################
	## source write_icc2_files outputs from DC and commit UPF  
	################################################################
	if {[file exists ${DCRM_RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}/${DESIGN_NAME}.icc2_script.tcl]} {
		## Read in design output files from Design Compiler's write_icc2_files command
		puts "RM-info: Sourcing [which ${DCRM_RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}/${DESIGN_NAME}.icc2_script.tcl]"
		rm_source -file ${DCRM_RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}/${DESIGN_NAME}.icc2_script.tcl

		if {$EARLY_DATA_CHECK_POLICY != "none"} {
			## Design check manager
			set_early_data_check_policy -policy $EARLY_DATA_CHECK_POLICY -if_not_exist
		}

		puts "RM-info: Running commit_upf"
		commit_upf
	} else {
		puts "RM-error : ${DCRM_RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}/${DESIGN_NAME}.icc2_script.tcl is not found." 
		puts "RM-warning : ${DCRM_RESULTS_DIR}/${DCRM_FINAL_DESIGN_ICC2}/${DESIGN_NAME}.icc2_script.tcl is required for DC_ASCII flow." 
	}


	################################################################
	## Additional floorplan constraints  
	################################################################
	#  If DEF_FLOORPLAN_FILES is provided but can not cover certain floorplan constraint types, then they can be provided here.
	#  If initialize_floorplan is used, additional floorplan constraints can be provided here. 
	#  For example, bounds, pin guides, or route guides, etc
	rm_source -file $TCL_ADDITIONAL_FLOORPLAN_FILE -optional -print "TCL_ADDITIONAL_FLOORPLAN_FILE"
	
	## IO, and macro placement: Refer to examples/init_design.flat_design_planning_example.tcl for sample commands

