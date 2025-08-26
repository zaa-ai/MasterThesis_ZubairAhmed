###################################################
# 
# digtop.dft_signal_defs.tcl
#
###################################################

set_app_var test_validate_test_model_connectivity true
set_app_var hdlin_enable_rtldrc_info true
set_app_var test_default_strobe 8
set_app_var test_default_period 40

set_dft_drc_configuration -internal_pins enable 


########################################################
# Define Scan and Reset Ports
########################################################

set SCAN_CLK    [exec getPrjCfg.rb config/test/scan_clk]
set SCAN_SCK    [exec getPrjCfg.rb config/test/scan_sck]
set SCAN_ENABLE [exec getPrjCfg.rb config/test/scan_enable]
set TEST_MODE   [exec getPrjCfg.rb config/test/test_mode]
set SCAN_RES    [exec getPrjCfg.rb config/test/scan_res]
set SCAN_DIN1   [exec getPrjCfg.rb config/test/scan_din1] 
set SCAN_DOUT1  [exec getPrjCfg.rb config/test/scan_dout1]
set SCAN_DIN2   [exec getPrjCfg.rb config/test/scan_din2] 
set SCAN_DOUT2  [exec getPrjCfg.rb config/test/scan_dout2]
set SCAN_DIN3   [exec getPrjCfg.rb config/test/scan_din3] 
set SCAN_DOUT3  [exec getPrjCfg.rb config/test/scan_dout3]
set PORB        [exec getPrjCfg.rb config/test/porb]

########################################################
# Define internal hookup pins
########################################################

set SCAN_ENABLE_HOOK      [filter [get_pins -hier] -regexp "@full_name =~ pure_and_scan_enable/and_inst/Z"]
set SCAN_MODE_HOOK        [filter [get_pins -hier] -regexp "@full_name =~ .*SCAN_reg/Q"]
set SCAN_COMPRESSION_HOOK [filter [get_pins -hier] -regexp "@full_name =~ .*COMPRESSION_reg/Q"]
set IDDQ_MODE_HOOK        [filter [get_pins -hier] -regexp "@full_name =~ .*VDD_DIS_reg/Q"]

########################################################
# Set don't scan elements
########################################################
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*SCAN_reg"]              ;# 1 FF 
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*COMPRESSION_reg"]       ;# 1 FF
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*VDD_DIS_reg"]           ;# 1 FF
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*VDD_ILOAD_DIS_reg"]     ;# 1 FF
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*VDD_RDIV_DIS_reg"]      ;# 1 FF
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*DISABLE_OSC_reg"]       ;# 1 FF
set_scan_element false [filter [get_cell -hier]  -regexp "@full_name =~ .*clkref_divided_reg_*"]   ;# 3 FF

########################################################
# Set dft signals
########################################################

set_dft_signal -view existing -type ScanClock   -port $SCAN_CLK    -timing {10 30}
set_dft_signal -view existing -type ScanClock   -port $SCAN_SCK    -timing {10 30}
set_dft_signal -view existing -type ScanEnable  -port $SCAN_ENABLE -hookup_pin $SCAN_ENABLE_HOOK -active 1
set_dft_signal -view spec     -type ScanEnable  -port $SCAN_ENABLE -hookup_pin $SCAN_ENABLE_HOOK -active 1
set_dft_signal -view existing -type Constant    -port $TEST_MODE -active 1 
set_dft_signal -view existing -type Reset       -port $SCAN_RES  -active 0 
set_dft_signal -view existing -type Constant    -port $PORB      -active 1 


###############################################################
# 1) Scan Compression and Internal Scan Modes Without Autofix: 
#
# If you are not using the autofix feature, the first TestMode signal defined 
# in the script is used for scan compression, and the second one is ignored. 
# This is because, if you have only ScanCompression mode and InternalScan mode, 
# you need to define only one TestMode signal, which will toggle between 
# 1 and 0.  The SCAN_MODE signal should be defined as a constant, rather than
# as a test_mode, because it's an existing signal used to control the clocks
# and resets. 
#
# For example,
#
# set_dft_signal -view spec -type TestMode -port DFTMAX_MODE -active 1
# set_dft_signal -view existing -type Constant -port SCAN_MODE -active 1
###############################################################

set_dft_signal -view spec     -type TestMode   -hookup_pin $SCAN_COMPRESSION_HOOK -active 1
# If you wanna DC simulates the correctness of the scanprotocol than don't define the
# SCAN_MODE as constant 1
#set_dft_signal -view spec     -type Constant   -hookup_pin $SCAN_MODE_HOOK        -active 1 -test_mode all

set_dft_signal -view spec     -type ScanDataOut -port $SCAN_DOUT1
set_dft_signal -view spec     -type ScanDataIn  -port $SCAN_DIN1
set_dft_signal -view spec     -type ScanDataOut -port $SCAN_DOUT2
set_dft_signal -view spec     -type ScanDataIn  -port $SCAN_DIN2
set_dft_signal -view spec     -type ScanDataOut -port $SCAN_DOUT3
set_dft_signal -view spec     -type ScanDataIn  -port $SCAN_DIN3


########################################################
# Define Testmodes
########################################################

define_test_mode Internal_scan -usage scan
define_test_mode ScanCompression_mode -usage scan_compression

########################################################
# Set dft configruations
########################################################
set_dft_configuration  -connect_clock_gating enable

# remap to non-scan DFFs when not part of scan chain
set_dft_insertion_configuration -unscan true \
                                -map_effort high

set_scan_configuration  -chain_count 3 \
                        -add_lockup true \
                        -clock_mixing mix_clocks_not_edges \
                        -internal_clocks multi \
                        -insert_terminal_lockup true \
                        -mix_internal_clock_driver true \
                        -style multiplexed_flip_flop \
                        -test_mode all

# Number of chains for compressed chain count
# SI/SO 	max compressed 		chains max compressed chains
# pins 		(without OCC) 		(with OCC)*
# ----------------------------------------------------------
# 2		4
# 3		12			6
# 4		32			16
# 5		80			40
# 6		192			96
# 7		448			224
# 8		1024			512
# 9		2304			1152
# 10		5120			2560
# 11		11264			5632
# 12		24576			12288
# 13		32000			26624
# 14+		32000			32000
#
# * This column assumes that a single decompressor input is dedicated to compressed OCC clock chains. Additional dedicated clock
# chain decompressor inputs will further reduce the limit.

set_scan_compression_configuration -test_mode ScanCompression_mode \
                                   -base_mode Internal_scan \
                                   -xtolerance high \
                                   -min_power true \
                                   -inputs 3 \
                                   -outputs 3 \
                                   -chain_count 12 \
                                   -location i_logic_top/i_test/i_test_control

#set_dft_drc_rules -allow  {TEST-504 TEST-505}

read_test_protocol -section test_setup  ctl/${DESIGN_NAME}.atpg_std_init.ctl
