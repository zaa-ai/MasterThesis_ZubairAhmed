/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	spi_config				_spi_config;  
	spi_agent	          	_spi_agent;
	event					stop_uvm;
	check_service			_check_service;
	
	
	function new(string name = "");
		super.new(name);	
		_spi_config                       = new("spi_config");      
		_spi_config.is_active             = UVM_ACTIVE;                        
		_spi_config.checks_enable         = 1;
		_spi_config.coverage_enable       = 1;	
		
		_spi_config.cycle_time = 60ns; // 16.667 MHz
		_spi_config.inter_spi_transfer = 0ns;
		_spi_config.csn_to_sck = 50ns;
		_spi_config.sck_to_csn = 50ns;
		_spi_config.sck_init_value = 1'bz;
		_spi_config.use_finish_with_csn_active = 1;
	endfunction
	
endclass
