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
	
	spi_protocol_listener	_spi_protocol_listener;
	behaviour_checker		_spi_behaviour_checker;
	
	top_config				_top_config;
	
	command_buffer_creator		_command_buffer_creator;
    in_order_buffer_comparator  _buffer_comparator;
	check_register_reads		_check_register_reads;
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		
		/*###   SPI   ######################################################*/
		_top_config._spi_agent	= spi_agent::type_id::create("spi_agent", this);
		agent_factory #(spi_config)::register_config("spi_agent", _top_config._spi_config, this);
		
		/*###   buffer writer   ######################################################*/
		_top_config._buffer_writer_agent = buffer_writer_agent::type_id::create("buffer_writer_agent", this);
		agent_factory #(buffer_writer_config)::register_config("buffer_writer_agent", _top_config._buffer_writer_config, this);
		for (int i=0; i<DSI_CHANNELS; i++) begin
			_top_config._pdcm_buffer_writer_agent[i] = pdcm_buffer_writer_agent::type_id::create($sformatf("pdcm_buffer_writer_agent_%1d", i), this);
			agent_factory #(pdcm_buffer_writer_config)::register_config($sformatf("pdcm_buffer_writer_agent_%1d", i), _top_config._pdcm_buffer_writer_config[i], this);
			
			_top_config._crm_buffer_writer_agent[i] = buffer_writer_agent::type_id::create($sformatf("crm_buffer_writer_agent_%1d", i), this);
			agent_factory #(buffer_writer_config)::register_config($sformatf("crm_buffer_writer_agent_%1d", i), _top_config._crm_buffer_writer_config[i], this);
		
			_top_config._crm_packet_creator[i] = crm_packet_creator::type_id::create($sformatf("crm_packet_creator_%1d", i), this);
			_top_config._pdcm_packet_creator[i] = pdcm_packet_creator::type_id::create($sformatf("pdcm_packet_creator_%1d", i), this);
		end
		
		/*###   ELIP   ######################################################*/
		_top_config._elip_agent = elip_bus_agent::type_id::create("elip_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_agent", _top_config._elip_config, this);
		
		/*###   ELIP registers   ######################################################*/
		_top_config._elip_registers_agent = elip_bus_agent::type_id::create("elip_registers_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_registers_agent", _top_config._elip_registers_config, this);
		
		/*###   checking   ######################################################*/
		_spi_protocol_listener = spi_protocol_listener::type_id::create("spi_protocol_listener", this);
		_spi_behaviour_checker = behaviour_checker::type_id::create("behaviour_checker", this);
		
		_buffer_comparator = in_order_buffer_comparator::type_id::create("buffer_comparator", this);
		_top_config._buffer_comparator = _buffer_comparator;
		_command_buffer_creator = command_buffer_creator::type_id::create("command_buffer_creator", this);
        _top_config._command_buffer_creator = _command_buffer_creator;
		_check_register_reads = check_register_reads::type_id::create("check_register_reads", this);
		_top_config._check_register_reads = _check_register_reads;
        
        _top_config._tdma_scheme_upload_listener = tdma_scheme_upload_listener::type_id::create("tdma_scheme_upload_listener", this);
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		_top_config._spi_agent.analysis_port.connect(_spi_protocol_listener.analysis_export);
		_spi_protocol_listener.spi_command_frame_port.connect(_spi_behaviour_checker.analysis_export);
		_spi_protocol_listener.spi_command_frame_port.connect(_command_buffer_creator.analysis_export);
		_spi_protocol_listener.spi_command_frame_port.connect(_check_register_reads.frame_export);
		_command_buffer_creator.buffer_port.connect(_buffer_comparator.before_export);
		_top_config._buffer_writer_agent.analysis_port.connect(_buffer_comparator.after_export);
		_top_config._elip_agent.analysis_port.connect(_check_register_reads.elip_export);
		for (int i=0; i<DSI_CHANNELS; i++) begin
			_top_config._crm_packet_creator[i].sequencer = _top_config._crm_buffer_writer_agent[i].m_sequencer;
			_top_config._pdcm_packet_creator[i].sequencer = _top_config._pdcm_buffer_writer_agent[i].m_sequencer;
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
