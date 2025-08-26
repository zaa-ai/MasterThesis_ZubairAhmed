/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	spi_config				_spi_config;  
	spi_agent	          	_spi_agent;
	
	buffer_writer_agent		_buffer_writer_agent;
	buffer_writer_config	_buffer_writer_config;
	
	pdcm_buffer_writer_agent		_pdcm_buffer_writer_agent[DSI_CHANNELS-1:0];
	pdcm_buffer_writer_config	_pdcm_buffer_writer_config[DSI_CHANNELS-1:0];
	
	buffer_writer_agent		_crm_buffer_writer_agent[DSI_CHANNELS-1:0];
	buffer_writer_config	_crm_buffer_writer_config[DSI_CHANNELS-1:0];
	
	elip_bus_agent			_elip_agent;
	elip_bus_config			_elip_config;
	
	elip_bus_agent			_elip_registers_agent;
	elip_bus_config			_elip_registers_config;
	
    in_order_buffer_comparator _buffer_comparator;
	
	check_register_reads	_check_register_reads;
	
	crm_packet_creator			_crm_packet_creator[DSI_CHANNELS-1:0];
	pdcm_packet_creator			_pdcm_packet_creator[DSI_CHANNELS-1:0];
    
    tdma_scheme_upload_listener _tdma_scheme_upload_listener;
    command_buffer_creator      _command_buffer_creator;
	
	event					stop_uvm;
	
	function new(string name = "");
		super.new(name);	
		_spi_config                       = new("spi_config");      
		_spi_config.is_active             = UVM_ACTIVE;                        
		_spi_config.coverage_enable       = 1;
        _spi_config.cycle_time = 50ns; // 20.00 MHz
        _spi_config.csn_to_sck = 25ns;
        _spi_config.sck_to_csn = 0ns;
        
		
		_buffer_writer_config                 = new("buffer_writer_config");
		_buffer_writer_config.is_active       = UVM_PASSIVE;
		_buffer_writer_config.coverage_enable = 1;	
		for (int i=0; i<DSI_CHANNELS; i++) begin
			_pdcm_buffer_writer_config[i]                 = new($sformatf("pdcm_buffer_writer_config_%1d", i));
			_pdcm_buffer_writer_config[i].is_active       = UVM_ACTIVE;
			_pdcm_buffer_writer_config[i].coverage_enable = 1;	
			_crm_buffer_writer_config[i]                 = new($sformatf("crm_buffer_writer_config_%1d", i));
			_crm_buffer_writer_config[i].is_active       = UVM_ACTIVE;
			_crm_buffer_writer_config[i].coverage_enable = 1;	
		end
		
		_elip_config			= new("elip_config");
		_elip_config.is_active	= UVM_PASSIVE;
		
		_elip_registers_config				= new("elip_registers_config");
		_elip_registers_config.is_active	= UVM_ACTIVE;
		_elip_registers_config.coverage_enable = 1;	
	endfunction
	
endclass
