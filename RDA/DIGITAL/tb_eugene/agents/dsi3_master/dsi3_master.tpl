agent_name = dsi3_master
trans_item = dsi3_master_tr

# transaction variables
trans_var = rand logic data[$];
trans_enum_var = rand dsi3_pkg::dsi3_msg_type msg_type;
trans_enum_var = dsi3_pkg::dsi3_bit_time_e bit_time;

# constraints
trans_var_constraint = {data.size() == msg_type;}

byo_interface = dsi3_slave_if

driver_inc_inside_class 		= includes/dsi3_master_driver_inc_inside_class.sv

monitor_inc						= includes/dsi3_master_monitor_inc.sv
trans_inc_inside_class			= includes/dsi3_master_trans_inc_inside_class.svh
agent_config_inc_inside_class	= includes/dsi3_master_config_inc.svh
agent_append_to_build_phase		= includes/dsi3_master_agent_append_to_build_phase.svh

#generate_interface_instance = no
trans_generate_methods_inside_class = no
agent_config_generate_methods_after_class = no
agent_config_generate_methods_inside_class = no