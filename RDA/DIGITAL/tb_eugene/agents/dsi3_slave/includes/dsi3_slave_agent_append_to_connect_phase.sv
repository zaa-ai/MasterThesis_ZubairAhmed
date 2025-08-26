if (get_is_active() == UVM_ACTIVE) begin
	m_master_analysis_port.connect(m_master_subscriber.analysis_export);
	m_monitor.analysis_port.connect(analysis_port);
	m_master_subscriber.m_config = m_config;
	m_master_subscriber.m_sequencer = m_sequencer;
	
	m_crm_tdma_scheme_port.connect(m_master_subscriber.crm_tdma_fifo.analysis_export);
	m_pdcm_tdma_scheme_port.connect(m_master_subscriber.pdcm_tdma_fifo.analysis_export);
end

