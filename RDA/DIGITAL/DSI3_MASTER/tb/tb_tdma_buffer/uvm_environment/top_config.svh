/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	
	elip_bus_config			_elip_config;
	tdma_config				_tdma_config;
	
	tdma_agent				_tdma_agent;

	event					stop_uvm;
	
	check_elip				_check_elip;

	function new(string name = "");
		super.new(name);	
		_elip_config			= new("elip_config");
		_elip_config.is_active	= UVM_PASSIVE;
		_tdma_config			= new("tdma_config");
		_tdma_config.is_active	= UVM_ACTIVE;
	endfunction
	
endclass
