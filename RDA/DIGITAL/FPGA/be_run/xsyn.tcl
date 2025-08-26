# Some useful procedures
proc FileRead {fname} {
    if { [file readable $fname]} {
	set fileid [open $fname "r"]
	set contents [read $fileid]
	close $fileid
	return $contents
    }
}

set_param messaging.defaultLimit 1000

#set FPGA xc7k160
#set FPGA xc7k70
set FPGA xc7a100
set CREATE_REPORTS 1

if { $argc != 0 } {
    if { $argc > 1 } {
	puts "The script accepts max 1 argument."
	puts "1. no_reports -> Create no reports during synthesis"
	puts "Default : (no arguments) -> Reports are created."
	puts "Please try again."
	error "ERROR : too many arguments"
    } else {
	if { [lindex $argv 0] == "no_reports" } {
	    set CREATE_REPORTS 0
	    puts "** Reports will NOT be created **"
	} else {
	    puts "unknown argument"
	    puts "Allowed arguments :"
	    puts "1.  no_reports (Create no reports during synthesis)"
	    error "ERROR : unknown argument"
	}
    }
}

if {$FPGA == "xc7a100"} {
    set PART xc7a100tcsg324-2
}
if {$FPGA == "xc7k160"} {
    set PART xc7k160tfbg676-2
}
if {$FPGA == "xc7k70"} {
    set PART xc7k70tfbg676-2
}

set DESIGN $env(DESIGN)
puts "DESIGN is set to $DESIGN"
set DIGITAL $env(DIGITAL)

set DESIGN_NAME fpga
set IMPL FPGA
set outputDir ./results
set netlistDir $outputDir/gate_lvl_netlist

set DATE [exec date "+%Y_%m_%d_%H%M"]
set MCS_DIR mcs/mcs_$DATE

exec mkdir -p $outputDir
exec mkdir -p $MCS_DIR
exec mkdir -p $netlistDir

set RTL_SOURCE_FILES [FileRead ./results/digital.f]

set LOF  [open ./results/inc.lof r]

set INCF  [read $LOF]
close $LOF

set INC ""
foreach p $INCF {
    append INC " " [file dirname $p]
}
# Reading vhdl stuff
read_vhdl -lib digital [glob ../hdl/DIGITAL_TECH_pkg.vhd]
read_vhdl -lib digital [glob ../../rtl/DIGITAL_pkg.vhd]
read_vhdl -lib JTAG    [glob ../../TEST/rtl/*_pkg.vhd]
read_vhdl -lib OTP_MEM [glob ../../OTP_MEM/rtl/*.vhd]

foreach f $RTL_SOURCE_FILES {
    switch [file extension $f] {
	".v" {
	    read_verilog $f
	}
	".sv" {
	    read_verilog -sv $f
	}
	".vhd" {
	    read_vhdl $f
	}
	".vhdl" {
	    read_vhdl $f
	}
    }
}

read_verilog [glob ../UTILS/JTAG_MASTER/hdl/*.sv]
read_verilog [glob ../hdl/*.sv]
read_verilog [glob ../hdl/*.v]
	
set_property used_in_synthesis false [get_files  *xilinx.v]

######################################################
# IP Section (RAM/ROM) 
######################################################
# Create your IP with the Vivado IP catalog
set SRAM_NAME sram_3072x23
# Read in an existing IP customization
# or create an IP from scratch
read_ip [glob ../IP/$SRAM_NAME/$SRAM_NAME.xci]

# Set IP to use global synthesis (no DCP generated)
set_property generate_synth_checkpoint false [get_files $SRAM_NAME.xci]

# Need to generate output products for IP 
generate_target all [get_ips $SRAM_NAME]

#######################################################

set_param general.maxThreads 8

### constraints
if {$FPGA == "xc7a100"} {
    read_xdc constraints_7a.xdc
}

if {$FPGA == "xc7k160"} {
    read_xdc constraints_7k.xdc
}

if {$FPGA == "xc7k70"} {
    read_xdc constraints_7k.xdc
}

#synth_design -name $IMPL -top $DESIGN_NAME -include_dirs $INC -part $PART -retiming
synth_design -name $IMPL -top $DESIGN_NAME -include_dirs $INC -part $PART -constrset constrs_1 -verilog_define target_technology_FPGA

### IO mapping
if {$FPGA == "xc7a100"} {
    source ios_7a.tcl
}
if {$FPGA == "xc7k160"} {
    source ios_7k160.tcl
}
if {$FPGA == "xc7k70"} {
    source ios_7k70.tcl
}
#

# add debug core.
if {$env(DEBUGCORE) == 1} {
    source debug.xdc
}

#
#opt_design
#opt_design -bufg_opt
#opt_design -directive NoBramPowerOpt

place_design
if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_place_timing.rpt }

# may be skipped to optimize timing
#place_design -post_place_opt
#if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_place_opt_timing.rpt }

#run_drc
#phys_opt_design
phys_opt_design -hold_fix -critical_pin_opt -critical_cell_opt -retime
if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_place_phys_opt_timing.rpt }

#
if {$CREATE_REPORTS == 1} { report_timing_summary -file $outputDir/post_place_timing_summary.rpt }

#
# run router, report actual utilization and timing, write checkpoint design,
# run drc, write verilog and xdc out
#
## no improvement in timing with the following directives:
##-directive Explore / NoTimingRelaxation / HigherDelayCost / MoreGlobalIterations
route_design
if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_route_timing.rpt}

# may be skipped to optimize timing
phys_opt_design
if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_route_phys_opt1_timing.rpt }

# may be skipped to optimize timing
#phys_opt_design -hold_fix -retime -placement_opt -routing_opt
#if {$CREATE_REPORTS == 1} { report_timing -max_paths 10 -path_type summary -file $outputDir/post_route_phys_opt2_timing.rpt }
#
#phys_opt_design -directive ExploreWithHoldFix
#if {$CREATE_REPORTS == 1} {report_timing -max_paths 10 -path_type summary -file $outputDir/post_route_phys_opt3_timing.rpt }
#
if {$CREATE_REPORTS == 1} {
    report_timing_summary -file $outputDir/final_timing_summary.rpt
    report_timing -max_paths 10 -path_type summary -file $outputDir/final_timing.rpt

    report_clock_utilization -file $outputDir/clock_util.rpt
    report_utilization -file $outputDir/post_route_util.rpt
    report_power -file $outputDir/post_route_power.rpt
    report_drc -file $outputDir/post_imp_drc.rpt

}
write_verilog -force $outputDir/netlist.v
write_xdc -no_fixed_only -force $outputDir/${IMPL}_impl.xdc

write_debug_probes -force $outputDir/${IMPL}.ltx
write_bitstream -force $outputDir/${IMPL}.bit -raw_bitfile -mask_file -bin_file -readback_file

# export timesim netlist and sdf files
write_verilog -cell logic_top -force -mode timesim -include_xilinx_libs $netlistDir/logic_top_timesim_inc_libs.v
write_sdf -cell logic_top -force -process_corner fast $netlistDir/fpga_fast.sdf
write_sdf -cell logic_top -force -process_corner slow $netlistDir/fpga_slow.sdf

#
if {$CREATE_REPORTS == 1} {
    report_clocks
    report_clock_interaction
    report_clock_networks

    report_timing -setup
    report_timing -hold

}
exec cp vivado.log $MCS_DIR
write_bitstream -force $MCS_DIR/${IMPL}.bit
#write_cfgmem -force $MCS_DIR/${IMPL}.mcs -format MCS -size 32 -interface SPIx4 -loadbit "up 0 $MCS_DIR/${IMPL}.bit"

#
# Update the software section.
#
source elf_file/write_mmi.tcl
source elf_file/bram_info.tcl
write_mmi otp_sys_shell_32_imem0_inst
exec mv   otp_sys_shell_32_imem0_inst.mmi $outputDir/
