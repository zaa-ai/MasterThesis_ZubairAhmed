/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	
	dsi3_slave_agent		_dsi3_slave_agent;
	dsi3_slave_config		_dsi3_slave_config;
	
//	buffer_writer_config	_writer_config;
//	buffer_writer_agent		_writer_agent;

	event					stop_uvm;

	
	function new(string name = "");
		super.new(name);	
//		_writer_config                 = new("writer_config");
//		_writer_config.is_active       = UVM_PASSIVE;
//		_writer_config.checks_enable   = 1;
//		_writer_config.coverage_enable = 1;
		
		_dsi3_slave_config				= new("dsi3_slave_config");
		_dsi3_slave_config.is_active    = UVM_ACTIVE;
	endfunction
	
endclass
