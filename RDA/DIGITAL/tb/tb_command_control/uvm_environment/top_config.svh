/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	buffer_writer_config	_spi_writer_config;
	buffer_writer_agent		_spi_writer_agent;
	
	buffer_reader_config	_command_reader_config;
	buffer_reader_agent		_command_reader_agent;

	buffer_writer_config	_dsi_writer_config[DSI_CHANNELS-1:0];
	buffer_writer_agent		_dsi_writer_agent[DSI_CHANNELS-1:0];
	
	elip_bus_config			_elip_command_config;
	elip_bus_config			_elip_register_config;
	
	event					stop_uvm;
	check_register_write	_check_register_write;
	check_elip_command_write	_check_elip_command_write;
	
	check_dsi_command_writes	_check_dsi_command_writes[DSI_CHANNELS-1:0];
	
	virtual dsi_logic_if	_clear_crm_data_buffer;
	virtual dsi_logic_if	_clear_pdcm_data_buffer;
	virtual dsi_logic_if	_clear_command_buffer;
	
	
	frame_facade			_frame_facade;
//	check_ram_access		_check_ram_access;
	
	function new(string name = "");
		super.new(name);	
		_command_reader_config             = new("command_reader_config");
		_command_reader_config.is_active   = UVM_PASSIVE;
		
		_spi_writer_config                 = new("spi_writer_config");
		_spi_writer_config.is_active       = UVM_ACTIVE;
		_spi_writer_config.coverage_enable = 1;
		_spi_writer_config.is_completly_passive = 1'b1;
		
		for (int i = 0; i< DSI_CHANNELS; i++) begin
			_dsi_writer_config[i]                 = new($sformatf("dsi_writer_config_%0d", i));
			_dsi_writer_config[i].is_active       = UVM_PASSIVE;
			_dsi_writer_config[i].coverage_enable = 1;
		end
		
		_elip_command_config			= new("elip_command_config");
		_elip_command_config.is_active	= UVM_PASSIVE;
		_elip_register_config			= new("elip_register_config");
		_elip_register_config.is_active	= UVM_PASSIVE;
		
	endfunction
	
endclass
