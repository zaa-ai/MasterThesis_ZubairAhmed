/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	
	elip_bus_config			_elip_ram_config;
	elip_bus_config			_elip_jtag_config;
	elip_bus_agent			_elip_ram_agent;
	elip_bus_agent			_elip_jtag_agent;
	
	event					stop_uvm;
	
	function new(string name = "");
		super.new(name);	
		_elip_ram_config			= new("elip_ram_config");
		_elip_ram_config.is_active	= UVM_ACTIVE;
		_elip_jtag_config			= new("elip_jtag_config");
		_elip_jtag_config.is_active	= UVM_ACTIVE;
	endfunction
	
endclass
