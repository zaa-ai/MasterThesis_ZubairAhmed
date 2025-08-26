class spi_framing_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(spi_framing_seq)
	
	function new(string name = "");
		super.new("spi_framing");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm_denso denso_scheme = new();
		spi_csb_handler handlers[$];
		
		log_sim_description("Testcase for different types of SPI frames (CSB handling)", LOG_LEVEL_TOP);
		
		handlers = {per_word_csb_hander::create(), per_frame_csb_hander::create(), random_csb_hander::create()};
		
		foreach(handlers[i]) begin
			m_spi_agent.m_config.csb_handler = handlers[i]; 
			
			`create_and_send(register_check_ic_revision_seq)
			`create_and_send(crm_random_on_different_channels_seq)
			`create_and_send(random_pdcm_and_read_data_seq)
			`create_and_send(random_pdcm_and_read_multiple_packets_seq)
			#100us;
		end
	endtask
	
endclass
