begin
	spi_listener = new("spi_listener", this);
	m_behaviour_checker = behaviour_checker::type_id::create("m_behaviour_checker", this);
	m_dsi3_configuration_listener = new("m_dsi3_configuration_listener", this);
	m_tdma_scheme_upload_listener = tdma_scheme_upload_listener::type_id::create("m_tdma_scheme_upload_listener", this);
	
	for (int i=0; i<project_pkg::DSI_CHANNELS; i++) begin
	 	m_master_transmission_checker[i] = dsi3_master_transmission_checker::type_id::create($sformatf("m_master_transmission_checker_%1d", i), this);
	 	m_master_transmission_checker[i].set_channel(i);
	end
	
	m_transaction_recorder = dsi3_transaction_recorder::type_id::create("m_transaction_recorder", this);
	
	test_register_resetter = register_resetter::type_id::create("test_regmodel_resetter", this);
	edf_parameters = new();
end
