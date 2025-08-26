/**
 * Class: top_env
 * 
 * Top UVM environment for DSI3 block test case
 */
class top_env extends uvm_env;

	`uvm_component_utils(top_env)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	unit_test_top_config				_top_config;
	
	buffer_writer_agent		_writer_agent;
	
	buffer_reader_agent		_reader_agent;
	
	pdcm_buffer_writer_agent		_pdcm_data_writer_agent;
	buffer_writer_agent		_crm_data_writer_agent;
	
	elip_bus_agent			_elip_command_agent;
	elip_bus_agent			_elip_tdma_agent;
	
	frame_facade			_frame_facade;
	
	dsi3_master_configuration_listener m_dsi3_configuration_listener;
	
	ral_sys_device_registers	regmodel;
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db #(unit_test_top_config)::get(this, "", "_top_config", _top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")		
		end
		
		/*###   DSI slave   ######################################################*/
		_top_config._dsi3_slave_agent = dsi3_slave_agent::type_id::create("dsi3_slave_agent", this);
		agent_factory #(dsi3_slave_config)::register_config("dsi3_slave_agent", _top_config._dsi3_slave_config, this);
			
		/*###   DSI master   ######################################################*/
		_top_config._dsi3_master_agent = dsi3_master_agent::type_id::create("dsi3_master_agent", this);
		agent_factory #(dsi3_master_config)::register_config("dsi3_master_agent", _top_config._dsi3_master_config, this);
		
		/*###   DSI command writer   ######################################################*/
		_writer_agent = buffer_writer_agent::type_id::create("writer_agent", this);
		agent_factory #(buffer_writer_config)::register_config("writer_agent", _top_config._writer_config, this);
		
		/*###   DSI data writer   ######################################################*/
		_pdcm_data_writer_agent = pdcm_buffer_writer_agent::type_id::create("pdcm_data_writer_agent", this);
		agent_factory #(pdcm_buffer_writer_config)::register_config("pdcm_data_writer_agent", _top_config._pdcm_data_writer_config, this);
		
		_crm_data_writer_agent = buffer_writer_agent::type_id::create("crm_data_writer_agent", this);
		agent_factory #(buffer_writer_config)::register_config("crm_data_writer_agent", _top_config._crm_data_writer_config, this);
		
		/*###   DSI data reader   ######################################################*/
		_reader_agent = buffer_reader_agent::type_id::create("reader_agent", this);
		agent_factory #(buffer_reader_config)::register_config("reader_agent", _top_config._reader_config, this);
		
		/*###   ELIP   ######################################################*/
		_elip_command_agent = elip_bus_agent::type_id::create("elip_command_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_command_agent", _top_config._elip_command_config, this);
		
		_top_config._elip_register_agent = elip_bus_agent::type_id::create("elip_register_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_register_agent", _top_config._elip_register_config, this);
		
		_elip_tdma_agent = elip_bus_agent::type_id::create("elip_tdma_agent", this);
		agent_factory #(elip_bus_config)::register_config("elip_tdma_agent", _top_config._elip_tdma_config, this);
		
		/*###   checking   ######################################################*/
		_frame_facade = new("_frame_facade");
		_top_config._frame_facade = _frame_facade;
		
		_top_config._check_transmit = check_transmit::type_id::create("_check_transmit", this);
		
		_top_config._check_elip = check_elip_command_read_write::type_id::create("_check_elip", this);
		_top_config._check_elip_tdma = check_elip_tdma_access::type_id::create("_check_elip_tdma", this);
		
		_top_config._check_receive_pdcm = pdcm_check_receive::type_id::create("_check_receive_pdcm", this);
		_top_config._check_receive_crm = crm_check_receive::type_id::create("_check_receive_crm", this);
		
		m_dsi3_configuration_listener = new("m_dsi3_configuration_listener", this);
		
		uvm_reg::include_coverage("*", UVM_CVR_ALL);
		regmodel = ral_sys_device_registers::type_id::create("regmodel");
		regmodel.build();
		regmodel.lock_model();
		regmodel.reset();
	endfunction
	
	function void connect_phase(uvm_phase phase);
		_frame_facade.sequencer = _writer_agent.m_sequencer;
		_top_config._dsi3_master_agent.analysis_port.connect(_top_config._dsi3_slave_agent.m_master_analysis_port);
		
		/*###   command checking   ######################################################*/
		_frame_facade.frame_port.connect(_top_config._check_elip.frame_export);
		_elip_command_agent.analysis_port.connect(_top_config._check_elip.elip_export);
		
		/*###   tdma checking   ######################################################*/
		_frame_facade.frame_port.connect(_top_config._check_elip_tdma.frame_export);
		_elip_tdma_agent.analysis_port.connect(_top_config._check_elip_tdma.elip_export);
		
		/*###   DSI3 master checking   ######################################################*/
		_frame_facade.frame_port.connect(_top_config._check_transmit.frame_export);
		_top_config._dsi3_master_agent.analysis_port.connect(_top_config._check_transmit.dsi3_master_export);
		_top_config._check_transmit.slave_agent = _top_config._dsi3_slave_agent;
		
		/*###   received data checking   ######################################################*/
		_top_config._dsi3_slave_agent.analysis_port.connect(_top_config._check_receive_pdcm.dsi3_slave_export);
		_top_config._dsi3_master_agent.analysis_port.connect(_top_config._check_receive_pdcm.dsi3_master_export);
		_pdcm_data_writer_agent.analysis_port.connect(_top_config._check_receive_pdcm.buffer_writer_export);
		
		_top_config._dsi3_slave_agent.analysis_port.connect(_top_config._check_receive_crm.dsi3_slave_export);
		_top_config._dsi3_master_agent.analysis_port.connect(_top_config._check_receive_crm.dsi3_master_export);
		_crm_data_writer_agent.analysis_port.connect(_top_config._check_receive_crm.buffer_writer_export);
		
		m_dsi3_configuration_listener.configuration_port.connect(_top_config._dsi3_master_config.configuration_subscriber.analysis_export);
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
