/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class unit_test_top_config extends uvm_object;
	
	dsi3_slave_agent		_dsi3_slave_agent;
	dsi3_slave_config		_dsi3_slave_config;
	
	dsi3_master_config		_dsi3_master_config;
	dsi3_master_agent		_dsi3_master_agent;
	
	buffer_writer_config	_writer_config;
	pdcm_buffer_writer_config	_pdcm_data_writer_config;
	buffer_writer_config	_crm_data_writer_config;
	buffer_reader_config	_reader_config;
	
	elip_bus_config			_elip_command_config;
	elip_bus_config			_elip_register_config;
	elip_bus_agent			_elip_register_agent;
	elip_bus_config			_elip_tdma_config;

	event					stop_uvm;
	
	check_elip_command_read_write	_check_elip;
	check_elip_tdma_access	_check_elip_tdma;
	check_transmit			_check_transmit;
	pdcm_check_receive		_check_receive_pdcm;
	crm_check_receive		_check_receive_crm;
	frame_facade			_frame_facade;

	
	function new(string name = "");
		super.new(name);	
		_writer_config					= new("writer_config");
		_writer_config.is_active		= UVM_ACTIVE;
		
		_pdcm_data_writer_config				= new("pdcm_data_writer_config");
		_pdcm_data_writer_config.is_active		= UVM_PASSIVE;
		_pdcm_data_writer_config.is_completly_passive = 1'b0;
		_crm_data_writer_config					= new("crm_data_writer_config");
		_crm_data_writer_config.is_active		= UVM_PASSIVE;
		_crm_data_writer_config.is_completly_passive = 1'b0;
		
		_reader_config					= new("reader_config");
		_reader_config.is_active		= UVM_PASSIVE;
		
		_dsi3_slave_config				= new("dsi3_slave_config");
		_dsi3_slave_config.is_active    = UVM_ACTIVE;
		
		_dsi3_master_config				= new("dsi3_master_config");
		_dsi3_master_config.is_active   = UVM_PASSIVE;
		
		_elip_command_config			= new("elip_command_config");
		_elip_command_config.is_active	= UVM_PASSIVE;
		_elip_register_config			= new("elip_register_config");
		_elip_register_config.is_active	= UVM_ACTIVE;
		_elip_tdma_config				= new("elip_tdma_config");
		_elip_tdma_config.is_active		= UVM_PASSIVE;
	endfunction
	
endclass
