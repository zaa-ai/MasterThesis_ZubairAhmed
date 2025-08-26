class crm_multiple_broadcast_crms_in_one_command_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_multiple_broadcast_crms_in_one_command_frame_seq)
	
	function new(string name = "");
		super.new("crm_multiple_broadcast_crms_in_one_command_frame");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("multiple broadcast CRM TRANSMIT in one SPI command frame", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		repeat(3) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			end
		end
		check_dab(1'b1);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#1500us;
		check_dab(1'b1);
		transaction_recorder.expect_tr_count_for_all_channels(3);
		transaction_recorder.disable_recorder();
	endtask
endclass