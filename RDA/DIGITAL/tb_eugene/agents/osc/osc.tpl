agent_name = osc
trans_item = osc_tr

# transaction variables
trans_var	 	= rand	integer	freq; 
trans_var 		= rand	bit		enabled;		

if_port  = logic	CLK;
if_port  = logic	EN;

# config object values
config_var = int	initial_frequency	= 500000; // initial value to drive -> 500kHz
config_var = bit	initial_enabled		= 0; // initial value to drive -> enabled 

driver_inc_inside_class = includes/osc_driver_inc_inside_class.sv
monitor_inc				= includes/osc_monitor_inc.sv
