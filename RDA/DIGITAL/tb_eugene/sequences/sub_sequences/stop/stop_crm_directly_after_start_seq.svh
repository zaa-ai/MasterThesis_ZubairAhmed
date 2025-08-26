class stop_crm_directly_after_start_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_crm_directly_after_start_seq) 
	
	function new(string name = "");
		super.new("stop_crm_directly_after_start");
	endfunction
	
	virtual task run_tests();
		logic[project_pkg::DSI_CHANNELS-1:0] channel_started = 2'b0;
		
		log_sim_description("stop a pending CRM directly after start", LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
		transaction_recorder.enable_recorder();
		
		for (int delay = 20; delay < 70; delay++) begin
			log_sim_description($sformatf("stop a pending CRM directly after %0dns", delay * 50), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'd1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(delay * 50ns);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#500us;
			
			if(delay < 25) begin
				transaction_recorder.expect_tr_count(0, 1);
				transaction_recorder.expect_tr_count(1, 0);
			end
			if(delay > 60) begin
				transaction_recorder.expect_tr_count_for_all_channels(1);
			end
		
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if(channel_started[channel] == 1'b1) begin
					transaction_recorder.expect_tr_count(.channel(channel), .count(1));
				end
				
				if(transaction_recorder.get_master_tr_count(channel) == 1) begin
					channel_started[channel] = 1'b1;
				end
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		transaction_recorder.disable_recorder();
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass