/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	
	elip_bus_config			_elip_config;
	elip_bus_config			_elip_register_config;
	elip_bus_agent			_elip_register_agent;
	check_elip				_check_elip;
	
	event					stop_uvm;
	
	function new(string name = "");
		super.new(name);	
		_elip_config				= new("elip_config");
		_elip_config.is_active		= UVM_PASSIVE;
		
		_elip_register_config			= new("elip_register_config");
		_elip_register_config.is_active	= UVM_ACTIVE;
	endfunction
	
endclass
