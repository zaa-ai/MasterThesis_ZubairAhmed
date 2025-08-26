/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	pdcm_buffer_writer_config	_writer_config;
    pdcm_buffer_writer_agent	_writer_agent;
	
	buffer_reader_config	_reader_config;
	buffer_reader_agent		_reader_agent;
	
	elip_bus_config			_elip_register_config;
	elip_bus_config			_elip_buffer_config;
	elip_bus_agent			_elip_register_agent;
	
	
	event					stop_uvm;
	check_service			_check_service;
	
	function new(string name = "");
		super.new(name);	
		_writer_config                 = new("pdcm_writer_config");
		_writer_config.is_active       = UVM_ACTIVE;
		_writer_config.is_completly_passive = 1'b1;
		_reader_config                 = new("reader_config");
		_reader_config.is_active       = UVM_ACTIVE;
		_elip_buffer_config				= new("elip_buffer_config");
		_elip_buffer_config.is_active	= UVM_PASSIVE;
		_elip_register_config			= new("elip_register_config");
		_elip_register_config.is_active	= UVM_ACTIVE;
	endfunction
	
endclass
