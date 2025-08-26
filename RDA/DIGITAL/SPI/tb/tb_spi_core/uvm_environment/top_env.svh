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
	
	spi_config			_spi_config;
	spi_agent			_spi_agent;
	
	top_config			_top_config;
	
	check_service		_check_service;
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end

		_spi_agent		= spi_agent::type_id::create("spi_agent", this);
		_spi_config		= _top_config._spi_config;
		_top_config._spi_agent = _spi_agent;
		
		_check_service = check_service::type_id::create("_check_service", this);
		_top_config._check_service = _check_service;
		
		uvm_config_db #(spi_config)::set(this, "spi_agent", "config", _spi_config);
		if (_spi_config.is_active == UVM_ACTIVE )
			uvm_config_db #(spi_config)::set(this, "spi_agent.m_sequencer", "config", _spi_config);
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		_spi_agent.analysis_port.connect(_check_service.analysis_export);
	endfunction
	
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "End triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
