dsi3_master_subscriber	m_master_subscriber;
uvm_analysis_export #(dsi3_master_tr) m_master_analysis_port;

uvm_analysis_port#(tdma_scheme) m_crm_tdma_scheme_port;
uvm_analysis_port#(tdma_scheme) m_pdcm_tdma_scheme_port;

function void set_rxd_timing(timing_container timings);
	m_config.set_rxd_timing(timings);
	m_driver.set_iterator(timings.get_iterator());
endfunction

function timing_container get_rxd_timing();
	return m_config.get_rxd_timing();
endfunction

function timing_iterator get_rxd_timing_iterator();
	return m_driver.get_timing_iterator();
endfunction