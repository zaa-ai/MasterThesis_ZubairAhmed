#create_property bmm_info_memory_device cell -type string
# 100 MHz FPGA input clock
create_clock -period 10.000 -name clk100 -waveform {0.000 5.000} [get_ports CLK_100]
# 20 MHz SPI clock 
create_clock -period 45.000 -name sck -waveform {0.000 22.500} [get_ports  USB2SPI_SCK]
# 20 MHz SPI clock ond DBG_3 for Mariusz's Hardware
create_clock -period 45.000 -name sck_dbg -waveform {0.000 22.500} [get_ports  DBG_3]
# CLKREF
create_clock -period 250.000 -name clkref -waveform {0.000 125.00} [get_pins pure_mux_clkref_inst/o_y]


# SPI clock is not brought into the FPGA via clock-capable (CC) inputs so we need:
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets USB2SPI_SCK*  DBG_3]
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets USB2SPI_SS0O* DBG_4]

# Select signal for SPI clock
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets SW[1]]

create_generated_clock -name clk_18MHz   [get_pins clk_wiz_multiple_clk_inst/mmcm_adv_inst/CLKOUT0]
#create_generated_clock -name jtag_master_tck [get_pins clk_wiz_multiple_clk_inst/mmcm_adv_inst/CLKOUT1]


set_clock_groups	-name cg_async_groups \	
					-asynchronous \
					-group clk100 \
					-group {clk_18MHz} \
 					-group {sck sck_dbg}
 					

set_clock_groups    -name cg_physical_exclusive \
                    -physically_exclusive \
                    -group {sck} \
                    -group {sck_dbg}
                    
#set_false_path -to [get_pins -hierarchical -filter { NAME =~  "*i_utils_sync_ff_re*/q_reg/D" }]
set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*por_ff*" }]

#
# JIRA https://jira.elmos.de/browse/P52143-262?filter=-1
# Fixme: disabling the combinatorical loop for now, check if necessary when design has changed
#set_property ALLOW_COMBINATORIAL_LOOPS TRUE [get_nets i_logic_top/i_dsi3/generate_dsi3_blocks[0].i_dsi3_block/i_dsi3_core/i_dsi3_receive/i_dsi3_receive_data_collect/o_data*[15]_i_1_n_0]
#set_property ALLOW_COMBINATORIAL_LOOPS TRUE [get_nets i_logic_top/i_dsi3/generate_dsi3_blocks[1].i_dsi3_block/i_dsi3_core/i_dsi3_receive/i_dsi3_receive_data_collect/o_data*[15]_i_1__0_n_0]
#set_property ALLOW_COMBINATORIAL_LOOPS TRUE [get_nets i_logic_top/i_dsi3/generate_dsi3_blocks[2].i_dsi3_block/i_dsi3_core/i_dsi3_receive/i_dsi3_receive_data_collect/o_data*[15]_i_1__1_n_0]
#set_property ALLOW_COMBINATORIAL_LOOPS TRUE [get_nets i_logic_top/i_dsi3/generate_dsi3_blocks[3].i_dsi3_block/i_dsi3_core/i_dsi3_receive/i_dsi3_receive_data_collect/o_data*[15]_i_1__2_n_0]

# ADA ADC SPI input LTC1407
#set_input_delay  -clock clk_adc_if_73 2 [get_ports ADA_SDO]
#set_output_delay -clock clk_adc_if_73 0 [get_ports ADA_SCK]
#set_output_delay -clock clk_adc_if_73 0 [get_ports ADA_CONV]
                               
