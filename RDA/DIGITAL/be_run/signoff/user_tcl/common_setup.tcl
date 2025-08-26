puts "RM-Info: Running script [info script]\n"

source $env(PROJECT_HOME)/scripts/misc/tcl/procs.tcl

##########################################################################################
# Variables common to all reference methodology scripts
# Script: common_setup.tcl
# Version: O-2018.06-SP4 
# Copyright (C) 2007-2019 Synopsys, Inc. All rights reserved.
##########################################################################################

# Setup for getPrjCfg.rb...
# Create a symbolic link to your tech_config.xml in your top project folder
set TECH [exec getPrjCfg.rb -p tech]

set DESIGN_NAME                   "digtop"  ;#  The name of the top-level design

set DESIGN_REF_DATA_PATH          ""  ;#  Absolute path prefix variable for library/design data.
                                       #  Use this variable to prefix the common absolute path  
                                       #  to the common variables defined below.
                                       #  Absolute paths are mandatory for hierarchical 
                                       #  reference methodology flow.

##########################################################################################
# Hierarchical Flow Design Variables
##########################################################################################

set HIERARCHICAL_DESIGNS           "" ;# List of hierarchical block design names "DesignA DesignB" ...
set HIERARCHICAL_CELLS             "" ;# List of hierarchical block cell instance names "u_DesignA u_DesignB" ...

##########################################################################################
# Library Setup Variables
##########################################################################################

# For the following variables, use a blank space to separate multiple entries.
# Example: set TARGET_LIBRARY_FILES "lib1.db lib2.db lib3.db"

set ADDITIONAL_SEARCH_PATH        "$env(PROJECT_HOME)/be_run/syn/def $env(PROJECT_HOME)/config $env(PROJECT_HOME)/edf_registers $env(PROJECT_HOME)/rtl $env(PROJECT_HOME)/DATA_STORAGE/rtl"  ;#  Additional search path to be added to the default search path

set TARGET_LIBRARY_FILES          "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/max\[@type='gates'\]]\n[exec getPrjCfg.rb -r $TECH -p tech/lib/min\[@type='gates'\]]]"  ;#  Target technology logical libraries
#ToDo: add Macros to tech_config.xml
set ADDITIONAL_LINK_LIB_FILES     "[join [exec getPrjCfg.rb -r $TECH -p tech/lib/max\[@type='macro'\]]\n[exec getPrjCfg.rb -r $TECH -p tech/lib/min\[@type='macro'\]]]";# [exec getPrjCfg.rb -p tech/lib/no]"  ;#  Extra link logical libraries not included in TARGET_LIBRARY_FILES
				         
set MIN_LIBRARY_FILES             ""  ;#  List of max min library pairs "max1 min1 max2 min2 max3 min3"...

set MW_REFERENCE_LIB_DIRS         "[exec getPrjCfg.rb -r $TECH -p tech/mw/gates] \
				   [exec getPrjCfg.rb -r $TECH -p tech/mw/macros] \
				   [exec getPrjCfg.rb -r $TECH -p tech/mw/extra]"  ;#  Milkyway reference libraries (include IC Compiler ILMs here)

set MW_REFERENCE_CONTROL_FILE     ""  ;#  Reference Control file to define the Milkyway reference libs

set NDM_REFERENCE_LIB_DIRS        ""
set TECH_FILE                     "[exec getPrjCfg.rb -r $TECH -p tech/phys/tech_file]"  ;#  Milkyway technology file
set MAP_FILE                      "[exec getPrjCfg.rb -r $TECH -p tech/phys/mapfile]"  ;#  Mapping file for TLUplus
set TLUPLUS_MAX_FILE              "[exec getPrjCfg.rb -r $TECH -p tech/phys/captable/max]"  ;#  Max TLUplus file
set TLUPLUS_MIN_FILE              "[exec getPrjCfg.rb -r $TECH -p tech/phys/captable/min]"  ;#  Min TLUplus file

set MIN_ROUTING_LAYER            "[exec getPrjCfg.rb -r $TECH tech/phys/min_mtl]"   ;# Min routing layer
set MAX_ROUTING_LAYER            "[exec getPrjCfg.rb -r $TECH tech/phys/max_mtl]"   ;# Max routing layer

set LIBRARY_DONT_USE_FILE        "./user_tcl/lib_dont_use.tcl"   ;# Tcl file with library modifications for dont_use
set LIBRARY_DONT_USE_PRE_COMPILE_LIST ""; #Tcl file for customized don't use list before first compile
set LIBRARY_DONT_USE_PRE_INCR_COMPILE_LIST "";# Tcl file with library modifications for dont_use before incr compile

# Additional stuff
# For SDC/MCMM
set INPUT_DRIVER 	"[exec getPrjCfg.rb -r $TECH tech/phys/sdc_driving_cell]"

set MIN_LIBRARY_NAME  "[exec getPrjCfg.rb -r $TECH tech/lib/min\[@type='gates'\]/name]"
set MAX_LIBRARY_NAME  "[exec getPrjCfg.rb -r $TECH tech/lib/max\[@type='gates'\]/name]"
set MIN_LIBRARY_OC    "[exec getPrjCfg.rb -r $TECH tech/lib/min\[@type='gates'\]/oc]"
set MAX_LIBRARY_OC    "[exec getPrjCfg.rb -r $TECH tech/lib/max\[@type='gates'\]/oc]"

# Macro cells
set SRAM_INST		"i_logic_top/i_data_storage/i_ram_wrapper_ecc_with_bist/utils_sram_with_bist_inst/utils_sram_scan_shell_inst/sync_sram_inst/sram_inst"
set SRAM_MAX_LIB	"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='SRAM'\]/max/name]"
set SRAM_MIN_LIB	"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='SRAM'\]/min/name]"
set SRAM_MAX_OC         "[exec getPrjCfg.rb -r $TECH tech/lib\[@name='SRAM'\]/max/oc]"
set SRAM_MIN_OC         "[exec getPrjCfg.rb -r $TECH tech/lib\[@name='SRAM'\]/min/oc]"

# For future use... 
set OTP_INST		"i_logic_top/i_test/i_test_control/i_otp_wrapper/u_otpwrap_l3_top/u_otpwrap_l2_cpu/u_otpwrap_l1_jtag/u_otpwrap_l0_atpg/gen_tsmc_u_otp4kx12/u_otp4kx12"
set OTP_MAX_LIB		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='OTP'\]/max/name]"
set OTP_MIN_LIB		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='OTP'\]/min/name]"
set OTP_MAX_OC		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='OTP'\]/max/oc]"
set OTP_MIN_OC		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='OTP'\]/min/oc]"

set IPS_INST        "i_logic_top/i_test/i_test_control/i_otp_wrapper/u_otpwrap_l3_top/u_otpwrap_l2_cpu/u_otpwrap_l1_jtag/u_otpwrap_l0_atpg/gen_tsmc_u_otp4kx12/u_ips"
set IPS_MAX_LIB		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='IPS'\]/max/name]"
set IPS_MIN_LIB		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='IPS'\]/min/name]"
set IPS_MAX_OC		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='IPS'\]/max/oc]"
set IPS_MIN_OC		"[exec getPrjCfg.rb -r $TECH tech/lib\[@name='IPS'\]/min/oc]"


##########################################################################################
# Multivoltage Common Variables
#
# Define the following multivoltage common variables for the reference methodology scripts 
# for multivoltage flows. 
# Use as few or as many of the following definitions as needed by your design.
##########################################################################################

set PD1                          ""           ;# Name of power domain/voltage area  1
set VA1_COORDINATES              {}           ;# Coordinates for voltage area 1
set MW_POWER_NET1                "VDD1"       ;# Power net for voltage area 1

set PD2                          ""           ;# Name of power domain/voltage area  2
set VA2_COORDINATES              {}           ;# Coordinates for voltage area 2
set MW_POWER_NET2                "VDD2"       ;# Power net for voltage area 2

set PD3                          ""           ;# Name of power domain/voltage area  3
set VA3_COORDINATES              {}           ;# Coordinates for voltage area 3
set MW_POWER_NET3                "VDD3"       ;# Power net for voltage area 3

set PD4                          ""           ;# Name of power domain/voltage area  4
set VA4_COORDINATES              {}           ;# Coordinates for voltage area 4
set MW_POWER_NET4                "VDD4"       ;# Power net for voltage area 4

puts "RM-Info: Completed script [info script]\n"

