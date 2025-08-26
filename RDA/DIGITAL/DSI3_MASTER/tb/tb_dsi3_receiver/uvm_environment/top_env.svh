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
	
	dsi3_slave_agent		_dsi3_slave_agent;
	dsi3_slave_config		_dsi3_slave_config;
	
//	buffer_writer_config	_writer_config;
//	buffer_writer_agent		_writer_agent;
	
	top_config				_top_config;
	
	dsi3_master_configuration_listener m_dsi3_configuration_listener;
	ral_sys_device_registers	regmodel;
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db #(top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		
		/*###   DSI slave   ######################################################*/
		_dsi3_slave_agent = dsi3_slave_agent::type_id::create("dsi3_slave_agent", this);
		_top_config._dsi3_slave_agent = _dsi3_slave_agent;
		_dsi3_slave_config = _top_config._dsi3_slave_config;
		
		uvm_config_db #(dsi3_slave_config)::set(this, "dsi3_slave_agent", "config", _dsi3_slave_config);
		if (_dsi3_slave_config.is_active == UVM_ACTIVE )
			uvm_config_db #(dsi3_slave_config)::set(this, "dsi3_slave_agent.m_sequencer", "m_config", _dsi3_slave_config);
		
		
//		/*###   DSI buffer writer   ######################################################*/
//		_writer_agent = buffer_writer_agent::type_id::create("writer_agent", this);
//		_top_config._writer_agent = _writer_agent;
//		_writer_config = _top_config._writer_config;
//		
//		uvm_config_db #(buffer_writer_config)::set(this, "writer_agent", "config", _writer_config);
		
		/*###   checking   ######################################################*/
		
		m_dsi3_configuration_listener = new("m_dsi3_configuration_listener", this);
		
		uvm_reg::include_coverage("*", UVM_CVR_ALL);
		regmodel = ral_sys_device_registers::type_id::create("regmodel");
		regmodel.build();
		regmodel.lock_model();
		regmodel.reset();
	endfunction
	
	function void connect_phase(uvm_phase phase);
//		m_dsi3_configuration_listener.configuration_port.connect(_top_config._dsi3_master_config.configuration_subscriber.analysis_export);
		m_dsi3_configuration_listener.configuration_port.connect(_top_config._dsi3_slave_config.configuration_subscriber.analysis_export);
		m_dsi3_configuration_listener.regmodel = regmodel;
		
	endfunction
	
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		@_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
