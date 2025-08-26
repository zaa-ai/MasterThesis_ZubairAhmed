common_env_pkg::dsi3_master_configuration_subscriber configuration_subscriber;

function new(string name = "");
	super.new(name);
endfunction

function dsi3_pkg::dsi3_bit_time_e get_bit_time();
	return configuration_subscriber.get_bit_time();
endfunction
