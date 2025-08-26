agent_name = buffer_reader
trans_item = buffer_reader_tr

# transaction variables
trans_enum_var = rand buffer_reader_action_e	action; 
trans_var = rand logic[15:0]	data;
trans_var = rand logic[5:0]		ecc;
trans_var =      bit			empty;

trans_inc_before_class = includes/buffer_reader_trans_inc_before_class.sv

# constraints

byo_interface = buffer_reader_if

# config object values
config_var = virtual clk_reset_if vif_clk_rst;

driver_inc_inside_class 		= includes/buffer_reader_driver_inc_inside_class.sv
monitor_inc_inside_class		= includes/buffer_reader_monitor_inc_inside_class.sv
agent_append_to_connect_phase 	= includes/buffer_reader_agent_append_to_connect_phase.sv
monitor_inc						= includes/buffer_reader_monitor_inc.sv
agent_seq_inc           		= includes/buffer_reader_seq_inc.sv