if (get_is_active() == UVM_ACTIVE) begin
	m_master_subscriber = dsi3_master_subscriber::type_id::create("m_master_subscriber", this);
	m_master_analysis_port = new("m_master_analysis_port", this);
	m_driver.set_iterator(m_config.get_rxd_timing().get_iterator());
	
	m_crm_tdma_scheme_port = new("m_crm_tdma_scheme_port", this);
	m_pdcm_tdma_scheme_port = new("m_pdcm_tdma_scheme_port", this);
	
	m_config.configuration_subscriber = new("configuration_subscriber", this);
end

m_config.pdcm_scheme	= tdma_scheme_pdcm_factory::single_packet();
m_config.crm_scheme 	= tdma_scheme_crm::valid();
m_config.dm_scheme 		= tdma_scheme_dm::valid();