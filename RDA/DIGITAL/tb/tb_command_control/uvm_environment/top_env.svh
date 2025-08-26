/**
 * Class: top_env
 * 
 * TODO: Add class documentation
 */
class top_env extends uvm_env;

	`uvm_component_utils(top_env)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	buffer_writer_config	_spi_writer_config;
	buffer_writer_agent		_spi_writer_agent;
	
	buffer_reader_config	_command_reader_config;
	buffer_reader_agent		_command_reader_agent;
	
	buffer_writer_config	_dsi_writer_config[DSI_CHANNELS-1:0];
	buffer_writer_agent		_dsi_writer_agent[DSI_CHANNELS-1:0];
	
	elip_bus_config			_elip_command_config;
	elip_bus_config			_elip_register_config;
	elip_bus_agent			_elip_command_agent;
	elip_bus_agent			_elip_register_agent;
	
	top_config				_top_config;
	
	check_register_write	_check_register_write;
	check_elip_command_write _check_elip_command_write;
	check_dsi_command_writes _check_dsi_command_writes[DSI_CHANNELS-1:0];
	frame_facade			_frame_facade;
	
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		/*###   SPI buffer writer   ######################################################*/
		_spi_writer_agent = buffer_writer_agent::type_id::create("spi_writer_agent", this);
		_top_config._spi_writer_agent = _spi_writer_agent;
		_spi_writer_config = _top_config._spi_writer_config;
		
		uvm_config_db #(buffer_writer_config)::set(this, "spi_writer_agent", "config", _spi_writer_config);

		/*###   command buffer reader   ######################################################*/
		_command_reader_agent = buffer_reader_agent::type_id::create("command_reader_agent", this);
		_top_config._command_reader_agent = _command_reader_agent;
		_command_reader_config = _top_config._command_reader_config;
		
		uvm_config_db #(buffer_reader_config)::set(this, "command_reader_agent", "config", _command_reader_config);
		
		/*###   DSI buffer writer   ######################################################*/
		_dsi_writer_config = _top_config._dsi_writer_config;
		for (int i = 0; i< DSI_CHANNELS; i++) begin
			_dsi_writer_agent[i] = buffer_writer_agent::type_id::create($sformatf("dsi_writer_agent_%0d", i), this);
			
			uvm_config_db #(buffer_writer_config)::set(this, $sformatf("dsi_writer_agent_%0d", i), "config", _dsi_writer_config[i]);
		end
		_top_config._dsi_writer_agent = _dsi_writer_agent;
		
		/*###   ELIP   ######################################################*/
		_elip_command_agent = elip_bus_agent::type_id::create("elip_command_agent", this);
		_elip_command_config = _top_config._elip_command_config;
		uvm_config_db #(elip_bus_config)::set(this, "elip_command_agent", "config", _elip_command_config);
		_elip_register_agent = elip_bus_agent::type_id::create("elip_register_agent", this);
		_elip_register_config = _top_config._elip_register_config;
		uvm_config_db #(elip_bus_config)::set(this, "elip_register_agent", "config", _elip_register_config);
		
		/*###   checking   ######################################################*/
		_frame_facade = new("_frame_facade");
		_top_config._frame_facade = _frame_facade;
		
		_check_register_write = check_register_write::type_id::create("_check_register_write", this);
		_top_config._check_register_write = _check_register_write;
		
		_check_elip_command_write = check_elip_command_write::type_id::create("_check_elip_command_write", this);
		_top_config._check_elip_command_write = _check_elip_command_write;
		
		for(int channel=0; channel < DSI_CHANNELS; channel++) begin
			_check_dsi_command_writes[channel] = check_dsi_command_writes::type_id::create($sformatf("_check_dsi_command_writes_%1d", channel), this);
		end
		_top_config._check_dsi_command_writes = _check_dsi_command_writes;
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		_frame_facade.sequencer = _spi_writer_agent.m_sequencer;
		_frame_facade.frame_port.connect(_check_register_write.frame_export);
		_frame_facade.frame_port.connect(_check_elip_command_write.frame_export);
		
		_elip_command_agent.analysis_port.connect(_check_elip_command_write.elip_export);
		_elip_register_agent.analysis_port.connect(_check_register_write.elip_export);
		
		for(int channel=0; channel<DSI_CHANNELS; channel++) begin
			_frame_facade.frame_port.connect(_check_dsi_command_writes[channel].frame_export);
			_dsi_writer_agent[channel].analysis_port.connect(_check_dsi_command_writes[channel].buffer_export);
			_check_dsi_command_writes[channel].set_channel(channel);
			_check_dsi_command_writes[channel]._check_crm_data_buffer_clearing.vif = _top_config._clear_crm_data_buffer;
			_check_dsi_command_writes[channel]._check_pdcm_data_buffer_clearing.vif = _top_config._clear_pdcm_data_buffer;
			_check_dsi_command_writes[channel]._check_command_buffer_clearing.vif = _top_config._clear_command_buffer;
		end
	endfunction
	
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
