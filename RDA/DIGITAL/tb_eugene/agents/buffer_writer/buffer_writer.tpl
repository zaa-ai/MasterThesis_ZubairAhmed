agent_name = buffer_writer
trans_item = buffer_writer_tr

# transaction variables
trans_enum_var = rand buffer_writer_action_e	action; 
trans_var = rand logic[15:0]	data;
trans_var = rand logic[5:0]		ecc;
trans_var =      bit			full;
trans_var =      bit			nearly_full;

trans_inc_before_class = includes/buffer_writer_trans_inc_before_class.sv
trans_generate_methods_inside_class = no
trans_inc_inside_class  = includes/buffer_writer_trans_inc_inside_class.sv

# constraints

byo_interface = buffer_writer_if

# config object values
config_var = virtual clk_reset_if vif_clk_rst;
config_var = bit is_completly_passive = 1'b0;

driver_inc_inside_class 		= includes/buffer_writer_driver_inc_inside_class.sv
monitor_inc_inside_class		= includes/buffer_writer_monitor_inc_inside_class.sv
agent_append_to_connect_phase 	= includes/buffer_writer_agent_append_to_connect_phase.sv
monitor_inc						= includes/buffer_writer_monitor_inc.sv
agent_seq_inc          			 = includes/buffer_writer_seq_inc.sv