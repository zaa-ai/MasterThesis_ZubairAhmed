common_env_pkg::dsi3_master_configuration_subscriber configuration_subscriber;

function new(string name = "");
	super.new(name);
	begin
		default_slave_timing_container temp = new();
		rxd_timings = temp;
	end
endfunction : new

function int get_chip_time();
	return configuration_subscriber.get_chip_time();
endfunction

function void set_rxd_timing(timing_container timings);
	rxd_timings = timings;
endfunction

function timing_container get_rxd_timing();
	return rxd_timings;
endfunction

function tdma_scheme get_pdcm_scheme();
	return pdcm_scheme;
endfunction
  
function tdma_scheme get_crm_scheme();
	return crm_scheme;
endfunction
