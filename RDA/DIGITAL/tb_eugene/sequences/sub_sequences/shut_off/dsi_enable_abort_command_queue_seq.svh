class dsi_enable_abort_command_queue_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_abort_command_queue_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_abort_command_queue");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		log_sim_description("abort/clear command queue by DSI_ENABLE.TRE", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
		
		repeat(10) begin			
			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'd500;)
				repeat($urandom_range(5,10)) begin
					randcase
						1 : `spi_frame_create(spi_read_status_seq, )
						1 : `spi_frame_create(spi_crm_seq, channel_bits == 2'b11;)
						1 : `spi_frame_create(spi_dsi_wait_seq,)
						1 : `spi_frame_create(spi_pdcm_seq,)
						1 : `spi_frame_create(spi_sync_dsi_channels_seq,)
						1 : `spi_frame_create(spi_discovery_mode_seq,)
					endcase
				end
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#200us;
			disable_dsi_channels(2'b11);
			#100us;
			enable_dsi_channels(2'b11);
			#2ms;
			
			transaction_recorder.expect_tr_count_for_all_channels(0);
						
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;	
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end	
	endtask
endclass

