agent_name = dsi3_slave
trans_item = dsi3_slave_tr

# transaction variables
trans_var = rand logic[3:0]		data [$];
trans_var = rand int			tolerance_int; // 1000 => 100% => 0% tolerance
trans_var = rand int			chiptime;
trans_var = rand int			chips_per_symbol; // can be used to create single/double chip disturbances 
trans_enum_var = rand dsi3_pkg::dsi3_msg_type	msg_type;
trans_enum_var = rand error_injection_e	symbol_coding_error_injection;
trans_enum_var = rand error_injection_e	chip_length_error_injection;
trans_var = bit					symbol_coding_error;
trans_meta = real tolerance;

# constraints
trans_var_constraint = {tolerance_int inside {[900:1100]};}
trans_var_constraint = {data.size() inside {[1:2048]};}
trans_var_constraint = {msg_type inside {dsi3_pkg::DM, dsi3_pkg::CRM, dsi3_pkg::PDCM};}
trans_var_constraint = {chiptime inside {[2:10]};}
trans_var_constraint = {chips_per_symbol inside {[1:3]};}

if_port = dsi3_pkg::dsi3_wire cable;

# config object values
config_var = tdma_scheme pdcm_scheme;
config_var = tdma_scheme crm_scheme;
config_var = tdma_scheme dm_scheme;
config_var = real chip_time_error = 0.0; // error injection: % of chip_time that may have a wrong current value 
config_var = protected timing_container rxd_timings;

#uvm_seqr_class = yes

driver_inc_inside_class 		= includes/dsi3_slave_driver_inc_inside_class.sv
monitor_inc						= includes/dsi3_slave_monitor_inc.sv

agent_seq_inc                   = includes/dsi3_slave_seq_inc.sv
agent_append_to_connect_phase 	= includes/dsi3_slave_agent_append_to_connect_phase.sv
agent_append_to_build_phase   	= includes/dsi3_slave_agent_append_to_build_phase.sv
agent_inc_inside_class			= includes/dsi3_slave_agent_inc_inside_class.sv

trans_inc_before_class			= includes/dsi3_slave_trans_inc_before_class.sv
trans_inc_inside_class			= includes/dsi3_slave_trans_inc_inside_class.sv
#agent_config_inc_inside_class	= includes/dsi3_slave_config_inc_inside_class.sv

agent_config_generate_methods_inside_class = no
agent_config_generate_methods_after_class = no
agent_config_inc_inside_class	= includes/dsi3_slave_config_inc_inside_class.sv
agent_cover_inc_after_class		= includes/dsi3_slave_agent_cover_inc_after_class.sv

trans_generate_methods_inside_class = no
generate_interface_instance = no