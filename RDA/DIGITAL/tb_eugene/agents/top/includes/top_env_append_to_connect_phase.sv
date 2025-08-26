begin
	spi_reg_frontdoor frontdoor = spi_reg_frontdoor::type_id::create("spi-frontdoor");
	jtag_frontdoor _jtag_frontdoor = jtag_frontdoor::type_id::create("jtag-frontdoor");

	set_frontdoor(regmodel, frontdoor, m_spi_agent.m_sequencer, `STRING_OF(`LOGIC_TOP_PATH));
	set_frontdoor(test_regmodel, _jtag_frontdoor, m_jtag_master_agent.m_sequencer, "");
end

uvm_config_db #(edf_parameter_model)::set(null, "", "edf_parameter_model", edf_parameters);

// DSI3 bit time configuration listener
m_resb_agent.analysis_port.connect(m_dsi3_configuration_listener.resb_export);
spi_listener.spi_command_frame_port.connect(m_dsi3_configuration_listener.analysis_export);

for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
	m_dsi3_configuration_listener.configuration_port.connect(m_dsi3_master_config[i].configuration_subscriber.analysis_export);
	m_dsi3_configuration_listener.configuration_port.connect(m_dsi3_slave_config[i].configuration_subscriber.analysis_export);
	
	// Connect the DSI master agent monitor with the slave agent master transaction subscriber
	m_dsi3_master_agent[i].analysis_port.connect(m_dsi3_slave_agent[i].m_master_analysis_port);

	// DSI3 master transmission checker
	m_dsi3_configuration_listener.configuration_port.connect(m_master_transmission_checker[i].configuration_subscriber.analysis_export);
	m_dsi3_configuration_listener.configuration_port.connect(m_master_transmission_checker[i].configuration_export);
	m_master_transmission_checker[i].transaction_recorder = m_transaction_recorder;
	m_master_transmission_checker[i].edf_parameters = edf_parameters; 
	m_resb_agent.analysis_port.connect(m_master_transmission_checker[i].resb_export);
	m_rfc_agent.analysis_port.connect(m_master_transmission_checker[i].rfc_export);
	m_dsi3_master_agent[i].analysis_port.connect(m_master_transmission_checker[i].dsi3_master_export);
	m_dsi3_slave_agent[i].analysis_port.connect(m_master_transmission_checker[i].dsi3_slave_export);
	spi_listener.spi_command_frame_port.connect(m_master_transmission_checker[i].analysis_export);
end

// TDMA upload listener
m_resb_agent.analysis_port.connect(m_tdma_scheme_upload_listener.resb_export);
spi_listener.spi_command_frame_port.connect(m_tdma_scheme_upload_listener.analysis_export);

m_dsi3_configuration_listener.regmodel = regmodel;

// digital signals
m_tmode_config.initial_value = 1'b0;
m_resb_config.initial_value = 1'b0;
m_syncb_config.initial_value = 1'b1;

// SPI
m_spi_config.cycle_time = 50ns; // 20.00 MHz
m_spi_config.csn_to_sck = 50ns;
m_spi_config.sck_to_csn = 50ns;
m_spi_config.sck_init_value = 1'bz;

// JTAG
m_jtag_master_config.cycle_time = 125ns;

// connect spi protocol listener
m_spi_agent.analysis_port.connect(spi_listener.analysis_export);

// connect behaviour checker to spi listener
spi_listener.spi_command_frame_port.connect(m_behaviour_checker.analysis_export);

uvm_config_db #(dsi3_transaction_recorder)::set(null, "", "dsi3_transaction_recorder", m_transaction_recorder);

m_tmode_agent.analysis_port.connect(test_register_resetter.analysis_export);
test_register_resetter.reg_model = test_regmodel;
