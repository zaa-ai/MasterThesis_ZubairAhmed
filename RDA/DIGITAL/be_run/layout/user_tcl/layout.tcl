puts "RM-Info: Running script [info script]\n"

source -echo $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl
source -echo user_tcl/custom_icc_suppress_trivial_project_dependend_warnings.tcl

source -echo user_tcl/common_setup.tcl

set_app_var search_path "./sdc $search_path"

source -echo $env(PROJECT_HOME)/scripts/layout/tcl/icc/rm_setup/icc_setup.tcl

set ICC_CLOCK_OPT_CCD_EFFORT HIGH
############################################################
## changed settings in contrast to icc_setup.tcl
############################################################ 
set ICC_CREATE_GR_PNG             TRUE		       	 	;# line 131
set ICC_IN_DEF_FILE               "../syn/def/digtop.def"   	;# line 213
set ICC_IN_FLOORPLAN_USER_FILE    "icc_in_floorplan_user.tcl"   ;# line 217.
set CUSTOM_CONNECT_PG_NETS_SCRIPT "connect_pg_nets.tcl"      	;# line 226   
set ICC_PORT_PROTECTION_DIODE_EXCLUDE_PORTS "A_OTP_EHV A_OTP_VRR A_OTP_VREF A_OTP_VPP"  ;# line 376
set ANA_NETS_NUM	 	  [llength $ICC_PORT_PROTECTION_DIODE_EXCLUDE_PORTS] ;# line 24 but needs $ICC_PORT_PROT....

###############################
## ELMOS Flow Variables for design planning
###############################
set TAPCELLNAME 		  [exec getPrjCfg.rb -r $TECH tech/phys/tapcel]
set ICC_TIE_HIGH_CELL		  [exec getPrjCfg.rb -r $TECH tech/phys/tiehi]
set ICC_TIE_LOW_CELL		  [exec getPrjCfg.rb -r $TECH tech/phys/tielo]

############################################################# 
# Settings for better ICC/PrimeTime correlation
# Documented in Confluence
############################################################# 
set dont_bind_unused_pins_to_logic_constant true
set disable_auto_time_borrow true
set ignore_clock_input_delay_for_skew true
set allow_input_delay_min_greater_than_max true
set timing_disable_recovery_removal_checks false
set high_fanout_net_threshold 0
set timing_edge_specific_source_latency true
set timing_enable_non_sequential_checks true
set timing_use_clock_specific_transition false
set rc_degrade_min_slew_when_rd_less_than_rnet true

###############################
## check_signoff_correlation  Variables
###############################
set PT_DIR "/common/run/synopsys/primetime/S-2021.06-SP5/bin"                                   ;# path to PrimeTime bin directory
set PT_SDC_FILE ""                              ;# optional file in case PrimeTime has a different SDC that what is available in the IC Compiler database
set STARRC_DIR "/common/run/synopsys/starrc/O-2018.06-SP5-2/bin"                               ;# path to StarRC bin directory
set STARRC_MAX_NXTGRD $env(TCAD_GRD_FILE_MAX)                        ;# MAX NXTGRD file
set STARRC_MIN_NXTGRD $env(TCAD_GRD_FILE_MIN)                        ;# MIN NXTGRD file
set STARRC_MAP_FILE "$MAP_FILE"                 ;# NXTGRD mapping file, defaults to TLUPlus mapping file, but could be different
set ICC_SIGNOFF_OPT_CHECK_CORRELATION_POSTROUTE_SCRIPT "" ;# a file to be sourced to run at check_signoff_correlation end of route_opt_icc step; 

############################################################
## Customized Constraint Script for Core Commands (Optional)
############################################################ 
set CUSTOM_INIT_DESIGN_PRE_SCRIPT          ""    ;# if specified, will be sourced before the read_def command;
set CUSTOM_PLACE_OPT_PRE_SCRIPT            "custom_place_opt_pre.tcl"    ;# if specified, will be sourced right before the place_opt core command;
set CUSTOM_PLACE_OPT_POST_SCRIPT           ""    ;# if specified, will be sourced right after the place_opt core command;
set CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT        ""    ;# if specified, will be sourced right before the clock_opt -concurrent_clock_and_data core command;
set CUSTOM_CLOCK_OPT_CCD_PRE_SCRIPT        ""    ;# if specified, will be sourced right before the clock_opt -concurrent_clock_and_data core command;
set CUSTOM_CLOCK_OPT_CCD_POST_SCRIPT       ""    ;# if specified, will be sourced right after the clock_opt -concurrent_clock_and_data core command;
set CUSTOM_CLOCK_OPT_ROUTE_PRE_SCRIPT      ""    ;# if specified, will be sourced before the route_group -all_clock_nets command;
set CUSTOM_CLOCK_OPT_ROUTE_PRE_CTO_SCRIPT  ""    ;# if specified, will be sourced before the optimize_clock_tree command;
set CUSTOM_CLOCK_OPT_ROUTE_POST_CTO_SCRIPT ""    ;# if specified, will be sourced after the optimize_clock_tree command;
set CUSTOM_ROUTE_PRE_SCRIPT                "custom_route_pre_script.tcl"    ;# if specified, will be sourced before the route_opt -initial_route_only command;
set CUSTOM_ROUTE_POST_SCRIPT               "custom_route_opt_post_script.tcl"  ;# if specified, will be sourced after the route_opt -initial_route_only command;
set CUSTOM_ROUTE_OPT_PRE_SCRIPT            ""    ;# if specified, will be sourced right before the route_opt core command;
set CUSTOM_ROUTE_OPT_POST_SCRIPT           ""    ;# if specified, will be sourced right after the route_opt core command;
set CUSTOM_FOCAL_OPT_PRE_SCRIPT            ""    ;# if specified, will be sourced before the focal_opt core commands;
set CUSTOM_FOCAL_OPT_POST_SCRIPT           ""    ;# if specified, will be sourced after the focal_opt core commands;
set CUSTOM_CHIP_FINISH_POST_SCRIPT         "chip_finish_post.tcl"    ;# if specified, will be sourced before the route_opt -inc -size_only command;
set CUSTOM_METAL_FILL_PRE_SCRIPT           "metal_fill_pre.tcl"    ;# if specified, will be sourced before insert_metal_filler command;
set ICC_UNCERTAINTY_PRECTS_FILE		       "icc_uncertainty_prects_file" ;# Pre-cts uncertainty file used during place_opt
set ICC_UNCERTAINTY_POSTCTS_FILE	       "icc_uncertainty_postcts_file" ;# Post-cts uncertainty file used during post-CTS optimization and route_opt
############################################################ 

puts "This Target: $env(THIS_TARGET)"
switch $env(THIS_TARGET) {
    icc {
        puts "### GUI ready ###"
        return
    }
    metal_fill_icc {
	# By default, the 
	# insert_metal_filler command fills all the routing layers from metal1 to the 
	# top metal layer. If the router is constrained not to use some metal layers, 
	# then insert_metal_filler stops working.
	set MIN_ROUTING_LAYER     "METAL1"
	set MAX_ROUTING_LAYER     "METAL5"    
	source -echo [which $env(THIS_TARGET).tcl]
    }
    eco_icc {
	    # Run this step after the PT/DMSA Flow to fix max_transition violations.
	    set ICC_ECO_FLOW        "UNCONSTRAINED"
	    set ICC_ECO_FILE        "../signoff/results/eco_changes.tcl"
	    set ICC_ECO_FLOW_TYPE   "pt_drc_setup_fixing_tcl"
	    source -echo [which $env(THIS_TARGET).tcl]
	    close_mw_cel
	    set ICC_METAL_FILL_CEL  $ICC_ECO_CEL
	    source -echo [which outputs_icc.tcl]
    }
    outputs_icc {
	set FILLER_CELL_METAL     "$FILLER_CELL_METAL digital_iso"
	source -echo [which $env(THIS_TARGET).tcl]
    }    
    default {
        if {[file exists [which $env(THIS_TARGET).tcl]]} {
            source -echo [which $env(THIS_TARGET).tcl]
        } else {
            puts "Error: Invalid target"
        }
    }
}

puts "RM-Info: Completed script [info script]\n"
if {$env(QUIT) != 0} {
  exit
}

print_message_info
