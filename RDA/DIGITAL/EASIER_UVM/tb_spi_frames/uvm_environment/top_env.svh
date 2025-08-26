/**
 * Class: top_env
 */
class top_env extends uvm_env;
	
	`uvm_component_utils(top_env)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction : new
		
	top_config	m_top_config;
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db #(top_config)::get(this, "", "m_top_config", m_top_config)) begin
			`uvm_error(get_type_name(), "Unable to get top_config")
		end
		m_top_config.m_spi_protocol_listener = spi_protocol_listener::type_id::create("spi_protocol_listener", this);
		
		m_top_config.m_spi_frame_subscriber = spi_frame_subscriber::type_id::create("frame_subscriber", this);
		m_top_config.m_spi_read_crm_subscriber = spi_read_crm_subscriber::type_id::create("crm_subscriber", this);
		m_top_config.m_spi_read_pdcm_subscriber = spi_read_pdcm_subscriber::type_id::create("pdcm_subscriber", this);
		
		m_top_config.m_tdma_scheme_upload_listener = tdma_scheme_upload_listener::type_id::create("tdma_listener", this);
		m_top_config.m_sequencer = logging_spi_sequencer::type_id::create("logging_spi_sequencer", this);
						
		m_top_config.m_behaviour_checker = behaviour_checker::type_id::create("behaviour_checker", this);
		
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			m_top_config.m_master_transmission_checker[i] = dsi3_master_transmission_checker::type_id::create($sformatf("master_checker_%1d", i), this);
			m_top_config.m_master_transmission_checker[i].set_channel(i);
			m_top_config.m_master_transmission_checker[i].edf_parameters = new();
		end
		
		m_top_config.m_transaction_recorder = dsi3_transaction_recorder::type_id::create("m_transaction_recorder", this);
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		m_top_config.m_spi_protocol_listener.spi_command_frame_port.connect(m_top_config.m_spi_frame_subscriber.analysis_export);
		m_top_config.m_spi_protocol_listener.spi_read_crm_port.connect(m_top_config.m_spi_read_crm_subscriber.analysis_export);
		m_top_config.m_spi_protocol_listener.spi_read_pdcm_port.connect(m_top_config.m_spi_read_pdcm_subscriber.analysis_export);
		
		for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
			m_top_config.m_spi_protocol_listener.spi_command_frame_port.connect(m_top_config.m_master_transmission_checker[i].analysis_export);
			m_top_config.m_master_transmission_checker[i].transaction_recorder = m_top_config.m_transaction_recorder;
		end
	endfunction
	
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		@m_top_config.stop_uvm;
		`uvm_info(this.get_type_name, "Simulation end triggered", UVM_INFO)
		#10us;
		phase.drop_objection(this);
	endtask : run_phase
	
endclass
