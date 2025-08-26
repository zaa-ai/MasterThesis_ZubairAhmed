#################################################################################
# Compile the Design
#
# Recommended Options:
#
#     -scan
#     -gate_clock (-self_gating)
#     -retime
#     -spg
#
# Use compile_ultra as your starting point. For test-ready compile, include
# the -scan option with the first compile and any subsequent compiles.
#
# Use -gate_clock to insert clock-gating logic during optimization.  This
# is now the recommended methodology for clock gating.
#
# Use -self_gating option in addition to -gate_clock for potentially saving 
# additional dynamic power, in topographical mode only. For registers 
# that are already clock gated, the inserted self-gate will be collapsed 
# with the existing clock gate. This behavior can be controlled 
# using the set_self_gating_options command
# XOR self gating should be performed along with clock gating, using -gate_clock
# and -self_gating options. XOR self gates will be inserted only if there is 
# potential power saving without degrading the timing.
# An accurate switching activity annotation either by reading in a saif 
# file or through set_switching_activity command is recommended.
# You can use "set_self_gating_options" command to specify self-gating 
# options.
#
# Use -retime to enable adaptive retiming optimization for further timing benefit.
#
# Use the -spg option to enable Design Compiler Graphical physical guidance flow.
# The physical guidance flow improves QoR, area and timing correlation, and congestion.
# It also improves place_opt runtime in IC Compiler.
#
# Note: In addition to -spg option you can enable the support of via resistance for 
#       RC estimation to improve the timing correlation with IC Compiler by using the 
#       following setting:
#
#       set_app_var spg_enable_via_resistance_support true
#
# You can selectively enable or disable the congestion optimization on parts of 
# the design by using the set_congestion_optimization command.
# This option requires a license for Design Compiler Graphical.
#
# The constant propagation is enabled when boundary optimization is disabled. In 
# order to stop constant propagation you can do the following
#
# set_compile_directives -constant_propagation false <object_list>
#
# Note: Layer optimization is on by default in Design Compiler Graphical, to 
#       improve the the accuracy of certain net delay during optimization.
#       To disable the the automatic layer optimization you can use the 
#       -no_auto_layer_optimization option.
#
#################################################################################
## RM+ Variable and Command Settings before first compile_ultra
#################################################################################
if { $OPTIMIZATION_FLOW == "hplp" || $OPTIMIZATION_FLOW == "tim" } {
    if {[shell_is_in_topographical_mode]} {
#ELMOS: leave this section in, its not part of the new flow
	# The following variable, when set to true, runs additional optimizations to improve the timing of  
	# the design at the cost of additional run time.
	set_app_var compile_timing_high_effort true

	# The following variable enables a mode of coarse placement in which cells are not distributed  
	# evenly  across the surface but are allowed to clump together for better QoR     
	set_app_var placer_max_cell_density_threshold 0.75        

  #Set the maximum utilization to 0.9 in congestion options 
  set_congestion_options -max_util 0.90

#ELMOS: leave this section in, its not part of the new flow
	# The following variable, when set to true, enables very high effort optimization to fix total negative slack 
	# Setting following variable to true may affect run time
	set_app_var psynopt_tns_high_effort true

	# Use the following variable to enable the physically aware clock gating 
	set_app_var power_cg_physically_aware_cg true
	
	#The following variable helps to reduce the total negative slack of the design
	set_app_var placer_tns_driven true

	# Enable low power placement.  
	# Low power placement affects the placement of cells, pulls them closer together, 
	# on nets with high switching activity to reduce the overall dynamic power of your design.  
        set_app_var power_low_power_placement true

        # In MCMM flow use set_scenario_options -dynamic_power true 
	#set_dynamic_optimization true
	#ELMOS: we use MCMM flow ...
	set_scenario_options -dynamic_power true

  # The set_qor_strategy -metric total_power recipe is focused on high-effort timing and total power reduction
  # The set_qor_strategy -metric timing recipe is focused only on high-effort timing reduction
  # The set_qor_strategy -reduced_effort option adjusts selected recipe for reduced runtime at the expense of timing QOR
  # A summary of application variables changed by this command are printed to the log file
      if { $OPTIMIZATION_FLOW == "hplp" && !$REDUCED_EFFORT_OPTIMIZATION_FLOW } {
        set_qor_strategy -metric total_power -stage synthesis
      } elseif { $OPTIMIZATION_FLOW == "hplp" && $REDUCED_EFFORT_OPTIMIZATION_FLOW } {
        set_qor_strategy -metric total_power -stage synthesis -reduced_effort
      } elseif { $OPTIMIZATION_FLOW == "tim" && !$REDUCED_EFFORT_OPTIMIZATION_FLOW } {
        set_qor_strategy -metric timing -stage synthesis
      } elseif { $OPTIMIZATION_FLOW == "tim" && $REDUCED_EFFORT_OPTIMIZATION_FLOW } {
        set_qor_strategy -metric timing -stage synthesis -reduced_effort
      }

    }

   if {[shell_is_dcnxt_shell]} {
                             # The following variable, when set to true, runs additional optimizations to improve the timing of  the design at the cost of additional run time, area and power. General recommendation is to enable enhanced timing optimization only after main compile. But for the case when design is having too many timing violations, user can enable below switch before main compile.
                             # set compile_enhanced_tns_optimization
    } 
        # The following variable enables register replication across the hierarchy by creating new ports
	# on the instances of the subdesigns if it is necessary to improve the timing of the design
	set_app_var compile_register_replication_across_hierarchy true 
}

if { $OPTIMIZATION_FLOW == "hc"} {
   if {[shell_is_in_topographical_mode]} {

       # This command enables congestion aware Global buffering based on Zroutebased estimation,
       # reducing congestion along narrow channels across macros. Enabling this feature may have 
       # runtime and QOR impact. Enable this variable on macro intensive designs with narrow channels.
       # set_ahfs_options -global_route true


       # With the following variables set, Zroute-based congestion-driven placement is enabled
       # instead of virtual route based estimation. 
       # Enabling this feature may have runtime impact. Enable this for highly congested designs
       # set_app_var placer_congestion_effort medium
       # set_app_var placer_enable_enhanced_router true

       # Enabling the variable can lead to lower congestion for designs that have congestion due to
       # multiplexing logic in the RTL. This variable is supported only in the initial compile step,
       # Not supported in incremental compile.
       set_app_var compile_prefer_mux true
   }
}
if { $OPTIMIZATION_FLOW == "rtm_exp"} {
  if {[shell_is_in_topographical_mode]} {
  
      set_host_options -max_cores 8
      # The following command overrides runtime-intensive user settings with settings designed
      # to improve runtime. Since the run time intensive optimizations are turned off it might 
      # impact QoR. You can use this as an exploration flow when run time is a concern.
      compile_prefer_runtime
  }
}
if {[shell_is_in_topographical_mode]} {

	# The following variable, when set to true, runs additional optimizations to improve the timing of  
	# the design at the cost of additional run time.
	#set_app_var compile_timing_high_effort true

if {[shell_is_dcnxt_shell]} {
  #################################################################################
  # Applying Required Settings for High Performance Cores
  #################################################################################
  # Use the set_technology and set_hpc_options command either before compile_ultra 
  # or before compile_ultra -incremental commands to set the core and stage 
  # specific settings for high performance cores. 
  # Refer to the "Applying Required Settings for High Performance Cores "
  # section in the Design Compiler User Guide for details.
  # Note: This is a Design Compiler NXT feature and is not supported in 
  # other flavors of the tool.
  # set_technology -node <n>              
  # set_hpc_options -core <core> -stage compile
  # Any individual settings applied after the set_hpc_options will 
  # override the recommended settings.
  }
}

if {[shell_is_in_topographical_mode]} {
  # Use the "-check_only" option of "compile_ultra" to verify that your
  # libraries and design are complete and that optimization will not fail
  # in topographical mode.  Use the same options as will be used in compile_ultra.

  # compile_ultra -scan -gate_clock -spg -check_only
}

# ELMOS: added option no_autoungroup
compile_ultra -scan -gate_clock -spg -no_autoungroup

#################################################################################
# Save Design after First Compile
#################################################################################

write -format ddc -hierarchy -output ${RESULTS_DIR}/${DCRM_COMPILE_ULTRA_DDC_OUTPUT_FILE}
