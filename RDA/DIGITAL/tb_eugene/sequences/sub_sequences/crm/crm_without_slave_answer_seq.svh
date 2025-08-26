class crm_without_slave_answer_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_without_slave_answer_seq)
	
	function new(string name = "");
		super.new("crm_without_slave_answer");
	endfunction : new
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		
		log_sim_description("CRM without slave answer", LOG_LEVEL_SEQUENCE);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("single CRM without answer at channel %0d", channel), 1);
			
			add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			check_dab(1'b1);
			
			read.expect_empty_data(2'(channel), {SCE});
			#100us;
		end
	endtask
endclass