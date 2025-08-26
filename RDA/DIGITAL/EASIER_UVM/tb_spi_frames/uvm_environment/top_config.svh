/**
 * Class: top_config
 * 
 * Configuration of the most top environment
 */
class top_config extends uvm_object;
	
	spi_frame_subscriber		m_spi_frame_subscriber;
	spi_read_crm_subscriber 	m_spi_read_crm_subscriber;
	spi_read_pdcm_subscriber 	m_spi_read_pdcm_subscriber;
	
	spi_protocol_listener		m_spi_protocol_listener;
	tdma_scheme_upload_listener m_tdma_scheme_upload_listener;
	
	dsi3_transaction_recorder 			m_transaction_recorder;
	dsi3_master_transmission_checker 	m_master_transmission_checker[$];
	
	logging_spi_sequencer 	m_sequencer;
	behaviour_checker 		m_behaviour_checker;
	
	event stop_uvm;
	
	function new(string name = "");
		super.new(name);	
	endfunction
	
	function void clear();
		m_sequencer.clear();
		m_spi_frame_subscriber.frames.delete();
		m_spi_read_crm_subscriber.reads.delete();
		m_spi_read_pdcm_subscriber.reads.delete();
		// invalidate all TDMA schemes
		m_tdma_scheme_upload_listener.set_default_schemes();
		m_transaction_recorder.clear_all();
	endfunction
	
endclass
