##########################################################################################
# Script: init_design.from_ascii.tcl
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
	## Read the verilog file(s)  
	################################################################
        if {$DESIGN_STYLE == "flat"} {
                read_verilog -top $DESIGN_NAME $VERILOG_NETLIST_FILES
                current_block $DESIGN_NAME

		if {$EARLY_DATA_CHECK_POLICY != "none"} {
			## Design check manager
			set_early_data_check_policy -policy $EARLY_DATA_CHECK_POLICY -if_not_exist
		}

                link_block
                save_lib
        } elseif {$DESIGN_STYLE == "hier"} {
		puts "RM-info: Sourcing [which init_design.from_ascii.hier.tcl]"
		rm_source -file init_design.from_ascii.hier.tcl
	}

	################################################################
	## Read UPF file(s)  
	################################################################
	## For golden UPF flow only (if supplemental UPF is provided): enable golden UPF flow before reading UPF
	if {[file exists [which $UPF_SUPPLEMENTAL_FILE]]} {
		set_app_options -name mv.upf.enable_golden_upf -value true ;# tool default false
	}

	if {[file exists [which $UPF_FILE]]} {
		load_upf $UPF_FILE

		## For golden UPF flow only (if supplemental UPF is provided): read supplemental UPF file
		if {[file exists [which $UPF_SUPPLEMENTAL_FILE]]} {
			load_upf -supplemental $UPF_SUPPLEMENTAL_FILE
		} elseif {$UPF_SUPPLEMENTAL_FILE != ""} {
			puts "RM-error: UPF_SUPPLEMENTAL_FILE($UPF_SUPPLEMENTAL_FILE) is invalid. Please correct it."
		}

		## Read the supply set file
		if {[file exists [which $UPF_UPDATE_SUPPLY_SET_FILE]]} {
			load_upf $UPF_UPDATE_SUPPLY_SET_FILE
		} elseif {$UPF_UPDATE_SUPPLY_SET_FILE != ""} {
			puts "RM-error: UPF_UPDATE_SUPPLY_SET_FILE($UPF_UPDATE_SUPPLY_SET_FILE) is invalid. Please correct it."
		}
	} elseif {$UPF_FILE != ""} {
		puts "RM-error : UPF file($UPF_FILE) is invalid. Please correct it."
	}

	################################################################
	## commit_upf  
	################################################################
	puts "RM-info: Running commit_upf"
	commit_upf


	################################################################
	## Floorplanning  
	################################################################

	####################################
	## Floorplanning : technology setup 
	####################################
	## Technology setup includes routing layer direction, offset, site default, and site symmetry
	#  - If TECH_FILE is used, technology setup is required 
	#  - If TECH_LIB is used and it does not contain the technology setup, then it is required
	#  Specify your technology setup script through TCL_TECH_SETUP_FILE. RM default is init_design.tech_setup.tcl.
	if {$TECH_FILE != "" || ($TECH_LIB != "" && !$TECH_LIB_INCLUDES_TECH_SETUP_INFO)} {
		rm_source -file $TCL_TECH_SETUP_FILE -optional -print "TCL_TECH_SETUP_FILE"
	}

	####################################
	## Floorplanning : from DEF 
	####################################
	## Floorplanning by reading $DEF_FLOORPLAN_FILES (supports multiple DEF files)
	#  Script first checks if all the specified DEF files are valid, if not, read_def is skipped
	if {$DEF_FLOORPLAN_FILES != ""} {
		set RM_DEF_FLOORPLAN_FILE_is_not_found FALSE
		foreach def_file $DEF_FLOORPLAN_FILES {
	      		if {![file exists [which $def_file]]} {
	      			puts "RM-error : DEF floorplan file ($def_file) is invalid."
	      			set RM_DEF_FLOORPLAN_FILE_is_not_found TRUE
	      		}
		}
	
	      	if {!$RM_DEF_FLOORPLAN_FILE_is_not_found} {

			set read_def_cmd "read_def $DEF_READ_OPTIONS [list $DEF_FLOORPLAN_FILES]"
	      		puts "RM-info: Creating floorplan from DEF file DEF_FLOORPLAN_FILES ($DEF_FLOORPLAN_FILES)"
			puts "RM-info: $read_def_cmd"
	      		eval ${read_def_cmd}

			redirect -var x {catch {resolve_pg_nets}} ;# workaround in case resolve_pg_nets returns warning that causes conditional to exit unexpectedly 
			puts $x
			if {[regexp ".*NDMUI-096.*" $x]} {
				puts "RM-error: UPF may have an issue. Please review and correct it."
			}

	      	} else {
	      		puts "RM-error : At least one of the DEF_FLOORPLAN_FILES specified is invalid. Please correct it."
	      		puts "RM-info: Skipped reading of DEF_FLOORPLAN_FILES"
	      	}
	}

	####################################
	## Floorplanning : from write_floorplan 
	####################################
	## Floorplanning by reading the write_floorplan generated TCL file, $TCL_FLOORPLAN_FILE
	if {$DEF_FLOORPLAN_FILES == "" && $TCL_FLOORPLAN_FILE != ""} {
		rm_source -file $TCL_FLOORPLAN_FILE
	}

	####################################
	## Floorplanning : initialize_floorplan
	#################################### 
	## Perform initialize_floorplan if neither DEF_FLOORPLAN_FILES nor TCL_FLOORPLAN_FILE is specified
	if {$DEF_FLOORPLAN_FILES == "" && $TCL_FLOORPLAN_FILE == ""} {
	      	puts "RM-info: creating floorplan using initialize_floorplan"

		initialize_floorplan
		## For pin placement, source your pin constraint script and run the place_pins -self command
		# 	place_pins -self ;# to place unplaced pins if needed
	}

	################################################################
	## Additional floorplan constraints  
	################################################################
	#  If DEF_FLOORPLAN_FILES is provided but can not cover certain floorplan constraint types, then they can be provided here.
	#  If initialize_floorplan is used, additional floorplan constraints can be provided here. 
	#  For example, bounds, pin guides, or route guides, etc
	rm_source -file $TCL_ADDITIONAL_FLOORPLAN_FILE -optional -print "TCL_ADDITIONAL_FLOORPLAN_FILE"
	
	## IO, and macro placement: Refer to examples/init_design.flat_design_planning_example.tcl for sample commands

	################################################################
	## SCANDEF  
	################################################################	
	if {[file exists [which $DEF_SCAN_FILE]]} {
		read_def $DEF_SCAN_FILE
	} elseif {$DEF_SCAN_FILE != ""} {
		puts "RM-error : DEF_SCAN_FILE($DEF_SCAN_FILE) is invalid. Please correct it."
	}

	################################################################
	## Timing constraints  
	################################################################
	## Specify a Tcl script to read in your TLU+ files by using the read_parasitic_tech command;
	#  Refer to examples/TCL_PARASITIC_SETUP_FILE.tcl for sample commands
	rm_source -file $TCL_PARASITIC_SETUP_FILE -optional -print "TCL_PARASITIC_SETUP_FILE"

	## Specify a Tcl script to create your corners, modes, scenarios and load respective constraints;
	#  Two examples are provided: 
	#  - examples/TCL_MCMM_SETUP_FILE.explicit.tcl: provide mode, corner, and scenario constraints; create modes, corners, 
	#    and scenarios; source mode, corner, and scenario constraints, respectively 
	#  - examples/TCL_MCMM_SETUP_FILE.auto_expanded.tcl: provide constraints for the scenarios; create modes, corners, 
	#    and scenarios; source scenario constraints which are then expanded to associated modes and corners
	rm_source -file $TCL_MCMM_SETUP_FILE -optional -print "TCL_MCMM_SETUP_FILE"
        ## Following lines are applicable for designs with physical hierarchy
        # Ignore the sub-blocks internal timing paths
        if {$DESIGN_STYLE == "hier" && $PHYSICAL_HIERARCHY_LEVEL != "bottom"} {
		set_timing_paths_disabled_blocks  -all_sub_blocks
        }

