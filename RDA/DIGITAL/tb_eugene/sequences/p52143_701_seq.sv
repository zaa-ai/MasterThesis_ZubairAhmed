class p52143_701_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(p52143_701_seq)
	
	function new(string name = "");
		super.new("p52143_701");
	endfunction
	
	virtual task run_tests();
		log_sim_description("synchronize and clear command buffer combinations", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		repeat(50) begin
			tdma_scheme_pdcm scheme = new();
			dsi3_crm_packet crm_packet_0 = random_crm_packet();
			dsi3_crm_packet crm_packet_1 = random_crm_packet();
			transaction_recorder.clear_all();

			add_slave_crm_scheme(0, tdma_scheme_crm::valid_with_data(crm_packet_0.get_word(0), crm_packet_0.get_word(1)));
			add_slave_crm_scheme(0, tdma_scheme_crm::no_answer());
			add_slave_crm_scheme(1, tdma_scheme_crm::valid_with_data(crm_packet_1.get_word(0), crm_packet_1.get_word(1)));
			add_slave_crm_scheme(1, tdma_scheme_crm::no_answer());
		
			
			if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			scheme.set_source_id_for_all_packets(dsi3_pkg::SID_8Bit);
			scheme.pdcm_period = 300;
			
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time inside {[50:200]};)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time inside {[10:150]};)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time inside {[300:500]};)
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time inside {[100:400]};)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			wait_for_dab();
			#50us;
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			wait_for_dab(2ms, .error_after_timeout(1'b1));
			transaction_recorder.expect_tr_count_for_all_channels(3);
			#50us;
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq,)
			`spi_frame_end
			#500us;
		end
		transaction_recorder.disable_recorder();
	endtask
	
	function dsi3_crm_packet random_crm_packet();
		dsi3_crm_packet packet = new();
		if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
		return packet;
	endfunction
endclass
