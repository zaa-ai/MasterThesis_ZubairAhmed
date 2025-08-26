################################################################################
# operating conditions
################################################################################
proc set_min_op_constraints {} {
    set_timing_derate -early 1.00
    set_timing_derate -late  1.05
}

proc set_max_op_constraints {} {
    set_timing_derate -early 0.95
    set_timing_derate -late  1.00
    set_timing_derate -late -cell_delay  1.255
	
}

proc set_bridge_max_op_constraints {} {
    set_timing_derate -early 0.95
    set_timing_derate -late  1.00
    #Timing derating for 150 degrees and 1.4V Low voltage level test, see: https://confluence.elmos.de/x/MEaZ
    set_timing_derate -late -cell_delay  1.255
}

################################################################################
# common constraints for all scenarios
################################################################################
proc set_common_constraints {} {
    global INPUT_DRIVER

    set_driving_cell -lib_cell $INPUT_DRIVER  [all_inputs]
    set_load 1 [all_outputs]
    source $::env(PROJECT_HOME)/be_run/syn/sdc/output_loads_from_starrc.sdc
}

################################################################################
# common constraints for scan_min/max scenarios
################################################################################
proc set_scan_constraints {} {
    #    global mode
    #    global corner
    #    puts "Running [dict get [info frame [info frame]] proc] for ${mode}_${corner}."
    if {[get_app_var synopsys_program_name] eq "dc_shell"} {
	set pos_clk_pin_name clocked_on
	set neg_clk_pin_name clocked_on
	set reset_pin_name clear
	set data_pin_name next_state
    } else {
	set pos_clk_pin_name CK
	set neg_clk_pin_name CKN
	set reset_pin_name RN
	set data_pin_name D
    }

    create_clock -name "scan_sck" -period 40 -waveform "10 30" [get_ports "I_SCK"]
    create_clock -name "scan_clk" -period 40 -waveform "10 30" [get_ports "I_BFWB"]
	
    if {[get_app_var synopsys_program_name] eq "dc_shell"} {
	set_clock_uncertainty -setup 1 [get_clocks]
	set_clock_uncertainty -hold  0.4 [get_clocks]
    }

    if {[get_app_var synopsys_program_name] ne "dc_shell"} {
	set_propagated_clock [get_clocks]
	set_clock_uncertainty -setup 0.3 [get_clocks]
	set_clock_uncertainty -hold  0.2  [get_clocks]
    }

    set ports_clock_root [filter_collection [get_attribute [get_clocks] sources] object_class==port]

    set_input_delay  -clock scan_clk 5 [remove_from_collection [all_inputs] ${ports_clock_root}]
    set_output_delay -clock scan_clk 5 [all_outputs]
    
    set_input_delay  -clock scan_sck 5 [remove_from_collection [all_inputs] ${ports_clock_root}]
    set_output_delay -clock scan_sck 5 [all_outputs]

   # set_case_analysis 1 [get_port { I_TMODE }]

    if {[get_app_var synopsys_program_name] eq "pt_shell"} {
	set_case_analysis 1 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "lib_pin_name == Q"]
    } else {
	set_case_analysis 1 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "name == Q"]
    }
	
    set_case_analysis 1 [get_port { I_TMODE }]
#	if {[get_app_var synopsys_program_name] eq "pt_shell"} {
#	# Clockdefinition for SCAN_RES to test min_pulse_width at reset pins SPEC 20us min; only for STA!!!
#	#create_clock -name "resb_clk"	-period 25000	-waveform { 0 12500 } [get_ports I_RESB]
#	#create_clock -name "tmode_clk"  -period 25000   -waveform { 0 12500 } [get_ports I_TMODE]
#	
##	set_clock_groups -asynchronous \
##		-group {scan_sck} \
##		-group {scan_clk} \
##		-group {resb_clk} \
##		-group {tmode_clk}
#	} else {
#	
#    set_clock_groups -asynchronous \
#    	-group {scan_sck} \
#    	-group {scan_clk} 
# 	}
    #set_false_path -from [get_ports {I_SCK I_BFWB I_RESB}] -through [filter [get_pins -hier] -regexp "@full_name =~ .*i_pad_mux_test_*.*test_reg_reg/$data_pin_name "]

    set_clock_sense -stop_propagation -clocks [all_clocks] [get_pins i_pad_mux_test_*/*/Z*]
    #    puts "Finished [dict get [info frame [info frame]] proc] for ${mode}_${corner}."
}
################################################################################
# common constraints for scan bridge scenario
################################################################################

proc set_bridge_scan_constraints {} {
    #    global mode
    #    global corner
    #    puts "Running [dict get [info frame [info frame]] proc] for ${mode}_${corner}."
    #   This mode is only for STA analysis and derating factor of 1.24 set in set_bridge_max_op_constraints
    if {[get_app_var synopsys_program_name] eq "dc_shell"} {
	set pos_clk_pin_name clocked_on
	set neg_clk_pin_name clocked_on
	set reset_pin_name clear
	set data_pin_name next_state
    } else {
	set pos_clk_pin_name CK
	set neg_clk_pin_name CKN
	set reset_pin_name RN
	set data_pin_name D
    }

    create_clock -name "scan_bridge_sck" -period 55 -waveform "0 27.5" [get_ports "I_SCK"]
    create_clock -name "scan_bridge_clk" -period 55 -waveform "0 27.5" [get_ports "I_BFWB"]
	
    if {[get_app_var synopsys_program_name] eq "dc_shell"} {
	set_clock_uncertainty -setup 1   [get_clocks]
	set_clock_uncertainty -hold  0.4 [get_clocks]
    }

    if {[get_app_var synopsys_program_name] ne "dc_shell"} {
	set_propagated_clock [get_clocks]
	set_clock_uncertainty -setup 0.3 [get_clocks]
	set_clock_uncertainty -hold   0.2 [get_clocks]
    }

    set ports_clock_root [filter_collection [get_attribute [get_clocks] sources] object_class==port]

    set_input_delay  -clock scan_bridge_sck 5 [remove_from_collection [all_inputs] ${ports_clock_root}]
    set_output_delay -clock scan_bridge_sck 5 [all_outputs]

    set_input_delay  -clock scan_bridge_clk 5 [remove_from_collection [all_inputs] ${ports_clock_root}]
    set_output_delay -clock scan_bridge_clk 5 [all_outputs]
	
    set_case_analysis 1 [get_port { I_TMODE }]
    
	if {[get_app_var synopsys_program_name] eq "pt_shell"} {
	set_case_analysis 1 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "lib_pin_name == Q"]
	} else {
	set_case_analysis 1 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "name == Q"]
	}

    # Due to muxing of inputs...we dont wanna have paths from scan_clk and reset through data pins of registers
    #set_false_path -from [get_ports {I_SCK I_BFWB I_RESB}] -through [filter [get_pins -hier] -regexp "@full_name =~ .*i_pad_mux_test_*.*test_reg_reg/$data_pin_name"]

    set_clock_sense -stop_propagation -clocks [all_clocks] [get_pins i_pad_mux_test_*/*/Z*]
    #    puts "Finished [dict get [info frame [info frame]] proc] for ${mode}_${corner}."
}

################################################################################
# common constraints for func_min/max scenarios
################################################################################
proc set_func_constraints {} {
    #    global mode
    #    global corner
    #    puts "Running [dict get [info frame [info frame]] proc] for ${mode}_${corner}."

    if {[get_app_var synopsys_program_name] eq "dc_shell"} {
	set pos_clk_pin_name clocked_on
	set neg_clk_pin_name clocked_on
	set reset_pin_name clear
	set data_pin_name next_state
    } else {
	set pos_clk_pin_name CK
	set neg_clk_pin_name CKN
	set reset_pin_name RN
	set data_pin_name D
    }
	
    # Virtual clock for CDC
    set CLK_VIRT_NAME V_CLK
    set CLK_VIRT_PER 44 
    set CLK_VIRT_WAVE "11 33" 
    
    create_clock \
	-name $CLK_VIRT_NAME \
	-period $CLK_VIRT_PER \
	-waveform $CLK_VIRT_WAVE
	
    set CLK_PERIOD_FUNC 44 ;# 22,73 MHz
    set CLK_PERIOD_PLL  55 ;# 18 MHz
    set CLK_PERIOD_SPI  59 ;# >16.9 MHz
    set CLK_PERIOD_TCK  50 ;# 20 MHz
    set CLK_PERIOD_IPS  6.5 ;# F_OSC max 154 MHz -> 6.49 ns
    set CLK_PERIOD_CLKREF 250 ;# CLKREF max. 4 MHz
    set CLK_PERIOD_CSB [expr 2*$CLK_PERIOD_SPI]

    # Clock Network
    set INPUT_DELAY     2
    set EXT_DELAY       2
    set CLK_RISE        1.0;#ToDo: mal reele Werte in Erfahrung bringen
    set CLK_FALL        1.0

    create_clock      -name "clk_osc_45" -period $CLK_PERIOD_FUNC   -waveform [list 0 [expr 0.45 * $CLK_PERIOD_FUNC]] [get_ports I_CLKOSC]
    create_clock -add -name "clk_osc_55" -period $CLK_PERIOD_FUNC   -waveform [list 0 [expr 0.55 * $CLK_PERIOD_FUNC]] [get_ports I_CLKOSC]

    create_clock      -name "clk_pll_40" -period $CLK_PERIOD_PLL   -waveform [list 0 [expr 0.4 * $CLK_PERIOD_PLL]] [get_ports I_CLKPLL]
    create_clock -add -name "clk_pll_60" -period $CLK_PERIOD_PLL   -waveform [list 0 [expr 0.6 * $CLK_PERIOD_PLL]] [get_ports I_CLKPLL]
    create_clock      -name "sck"        -period $CLK_PERIOD_SPI    -waveform [list [expr 0.25 * $CLK_PERIOD_SPI ] [expr 0.75 * $CLK_PERIOD_SPI]] [get_ports I_SCK   ]
    create_clock      -name "tck"        -period $CLK_PERIOD_TCK    -waveform [list 0 [expr 0.5 * $CLK_PERIOD_TCK ]] [get_ports I_BFWB  ]
    create_clock      -name "clkref"     -period $CLK_PERIOD_CLKREF -waveform [list 0 [expr 0.5 * $CLK_PERIOD_CLKREF ]] [get_ports I_CLKREF  ]
    create_clock      -name "csb"        -period $CLK_PERIOD_CSB    -waveform [list 0 [expr 0.5 * $CLK_PERIOD_SPI ]] [get_ports I_CSB]

    #IPS clocks
    if {[get_app_var synopsys_program_name] eq "pt_shell"} {
	create_clock -name "ips_clk"    -period $CLK_PERIOD_IPS -waveform [list 0 [expr 0.5 * $CLK_PERIOD_IPS ]] [get_pins -hier *u_ips/CLKOUT]
	create_clock -name "ips_ppclk"  -period $CLK_PERIOD_IPS -waveform [list 0 [expr 0.5 * $CLK_PERIOD_IPS ]] [get_pins -hier *u_ips/PPCLKOUT]
	#   create_generated_clock -divide_by 2 -name OTP_CLK -source [get_pins *otp_ck_reg/C*] [get_pins -hier *opt_ck_reg/Q]
    } else {
	create_clock -name "ips_clk"    -period $CLK_PERIOD_IPS -waveform [list 0 [expr 0.5 * $CLK_PERIOD_IPS ]] [get_flat_pins */*u_ips/CLKOUT]
	create_clock -name "ips_ppclk"  -period $CLK_PERIOD_IPS -waveform [list 0 [expr 0.5 * $CLK_PERIOD_IPS ]] [get_flat_pins */*u_ips/PPCLKOUT]
	#create_generated_clock -divide_by 2 -name OTP_CLK -source [get_flat_pins *otp_ck_reg/clocked_on] [get_flat_pins *otp_ck_reg/Q]
    }

	set_clock_groups -asynchronous \
		-group {clk_osc_45 } \
		-group {clk_osc_55 } \
		-group {clk_pll_40} \
		-group {clk_pll_60} \
		-group {sck csb} \
		-group {tck} \
		-group {ips_clk} \
		-group {ips_ppclk} \
		-group {clkref} \
	    -group {V_CLK}

    set_clock_groups -physically_exclusive \
	-group {clk_osc_45} \
	-group {clk_osc_55} \
	-group {clk_pll_40} \
	-group {clk_pll_60} 

    #Input/Output delays with virtual clock
    set ports_clock_root [filter_collection [get_attribute [get_clocks] sources] object_class==port]
    set_input_delay     -clock "V_CLK" 1 [remove_from_collection [all_inputs] ${ports_clock_root}]
    set_output_delay    -clock "V_CLK" 1 [all_outputs]
	
    # SPI timing JIRA https://jira.elmos.de/browse/P52144-205
    set_input_delay  20 -clock "sck" {I_SDI}
    set_output_delay  5 -clock "sck" {O_SDO}
    
    # Dedicated output delay for O_DSI_IDAC* Ports to align the edges
    foreach_in_collection clks [get_clocks clk_*] {
	    set_output_delay 6 -clock $clks -group_path DAC {O_DSI_IDAC[*]}
    }
	
    if { [get_app_var synopsys_program_name] eq "dc_shell" } {
	set_clock_uncertainty -setup 1    [get_clocks]
	set_clock_uncertainty -hold  0.4  [get_clocks]
	set_clock_transition  -fall $CLK_FALL [remove_from_collection [get_clocks] V_CLK]
	set_clock_transition  -rise $CLK_RISE [remove_from_collection [get_clocks] V_CLK]
    }

    if {[get_app_var synopsys_program_name] ne "dc_shell"} {
	set_propagated_clock [get_clocks]
	set_clock_uncertainty -setup 0.4  [get_clocks]
	set_clock_uncertainty -hold  0.3   [get_clocks]
    }
    
    # Functional mode -> Scan aus
    if {[get_app_var synopsys_program_name] eq "pt_shell"} {
	set_case_analysis 0 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "lib_pin_name == Q"]
    } else {
	set_case_analysis 0 [get_pins -of_objects [get_cells *SCAN_reg -hierarchical] -filter "name == Q"]
    }
 
    # False path from clocks to pad_mux_test test_vector inputs
    #set_false_path -from [all_clocks] -through [filter [get_pins -hier] -regexp "@full_name =~ .*i_pad_mux_test*.*test_vector.*"]
    #set_false_path -from [all_clocks] -through [filter [get_pins -hier] -regexp "@full_name =~ tmr_in_sync_reg_*.*/$data_pin_name"]

    # TCK through jtag_elip address and data_write
    #set_false_path -from I_BFWB -through [filter [get_pins -hier] -regexp "@full_name =~ .*jtag_elip/elip_addr.*"]
    #set_false_path -from I_BFWB -through [filter [get_pins -hier] -regexp "@full_name =~ .*jtag_elip/elip_data_write.*"]

    # Sysclocks through jtag_elip data read
    #set_false_path -from [get_ports {I_CLKPLL I_CLKOSC}] -through [filter [get_pins -hier] -regexp "@full_name =~ .*jtag_elip/o_data_shift_register.*"]

    # SPI -> SYS clock
    #set_false_path -from [get_ports {I_SCK}] -through [filter [get_pins -hier] -regexp "@full_name =~ .*i_spi/i_spi_core/o_data_received.*"]

    # SYS clock -> SPI
    #set_false_path -from [get_ports {I_CLKPLL I_CLKOSC}] -through [filter [get_pins -hier] -regexp "@full_name =~ .*i_spi.i_spi_core/i_ecc_dec_spi/o_data.*"]

    # Non-Unate pathes through pad_mux_test
    set_clock_sense -stop_propagation -clocks [all_clocks] [get_pins i_pad_mux_test_*/*/Z*]

}
