agent_name = real_signal
trans_item = real_signal_tr

trans_var  = rand longint value;
trans_var  = rand longint duration;
trans_var  = rand longint edge_duration;

if_port  = real PIN;

config_var = real init_value = 0.0;
config_var = time time_scale = 1ns; 
config_var = real value_scale = 0.01; 

driver_inc_inside_class = includes/real_signal_driver_inc_inside_class.sv
agent_seq_inc 			= includes/real_signal_seq_inc.sv 