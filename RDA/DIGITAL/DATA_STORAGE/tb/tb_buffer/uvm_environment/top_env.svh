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
	
	buffer_writer_config	_writer_config;
	buffer_writer_agent		_writer_agent;
	
	buffer_reader_config	_reader_config;
	buffer_reader_agent		_reader_agent;
	
	elip_bus_config			_elip_buffer_config;
	elip_bus_config			_elip_register_config;
	
	elip_bus_agent			_elip_buffer_agent;
	elip_bus_agent			_elip_register_agent;
	
	top_config				_top_config;
	
	check_service			_check_service;
	
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		/*###   buffer writer   ######################################################*/
		_writer_agent = buffer_writer_agent::type_id::create("buffer_writer_agent", this);
		_top_config._writer_agent = _writer_agent;
		_writer_config = _top_config._writer_config;
		
		uvm_config_db #(buffer_writer_config)::set(this, "buffer_writer_agent", "config", _writer_config);
		if (_writer_config.is_active == UVM_ACTIVE )
			uvm_config_db #(buffer_writer_config)::set(this, "buffer_writer_agent.m_sequencer", "m_config", _writer_config);
		
		/*###   buffer reader   ######################################################*/
		_reader_agent = buffer_reader_agent::type_id::create("buffer_reader_agent", this);
		_top_config._reader_agent = _reader_agent;
		_reader_config = _top_config._reader_config;
		
		uvm_config_db #(buffer_reader_config)::set(this, "buffer_reader_agent", "config", _reader_config);
		if (_reader_config.is_active == UVM_ACTIVE )
			uvm_config_db #(buffer_reader_config)::set(this, "buffer_reader_agent.m_sequencer", "m_config", _reader_config);
		
		/*###   ELIP   ######################################################*/
		_elip_buffer_agent = elip_bus_agent::type_id::create("elip_buffer_agent", this);
		_elip_buffer_config = _top_config._elip_buffer_config;
		uvm_config_db #(elip_bus_config)::set(this, "elip_buffer_agent", "config", _elip_buffer_config);
		
		_elip_register_agent = elip_bus_agent::type_id::create("elip_register_agent", this);
		_top_config._elip_register_agent = _elip_register_agent;
		_elip_register_config = _top_config._elip_register_config;
		uvm_config_db #(elip_bus_config)::set(this, "elip_register_agent", "config", _elip_register_config);
		if (_elip_register_config.is_active == UVM_ACTIVE )
			uvm_config_db #(elip_bus_config)::set(this, "elip_register_agent.m_sequencer", "m_config", _elip_register_config);
		
		/*###   checking   ######################################################*/
		_check_service = check_service::type_id::create("_check_service", this);
		_top_config._check_service = _check_service;
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		_writer_agent.analysis_port.connect(_check_service.writer_export);
		_reader_agent.analysis_port.connect(_check_service.reader_export);
		_elip_buffer_agent.analysis_port.connect(_check_service.buffer_elip_export);
	endfunction
	
	task run_phase(uvm_phase phase); //TODO: check if needed
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
