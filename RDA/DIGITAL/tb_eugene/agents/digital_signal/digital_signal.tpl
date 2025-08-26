agent_name = digital_signal
trans_item = digital_signal_tr

# transaction variables
trans_enum_var = rand digital_signal_t	_val; 
trans_var = logic					value;		

trans_inc_before_class = includes/digital_signal_trans_inc_before_class.sv
trans_inc_inside_class = includes/digital_signal_trans_inc_inside_class.sv

if_port  = logic D;

# config object values
config_var = logic initial_value	= 1'bx; // initial value to drive

driver_inc_inside_class = includes/digital_signal_driver_inc_inside_class.sv
monitor_inc				= includes/digital_signal_monitor_inc.sv