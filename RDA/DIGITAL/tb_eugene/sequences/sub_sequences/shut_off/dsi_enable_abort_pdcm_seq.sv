class dsi_enable_abort_pdcm_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_abort_pdcm_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_abort_pdcm");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet(16);
		scheme.pdcm_period = 300;
		scheme.packets[0].earliest_start_time = 20;
		scheme.packets[0].latest_start_time = 25;
		
		log_sim_description("abort PDCM using DSI_ENABLE register", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
		
		for (int aborted_channel=0; aborted_channel < project_pkg::DSI_CHANNELS; aborted_channel++) begin
			spi_read_pdcm_frame_seq read1, read2, read3;
			
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#420us;
			disable_dsi_channels(2'b01 << aborted_channel);
			#500us;

			`spi_frame_begin
				`spi_frame_send(read1, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;		
			`spi_frame_begin
				`spi_frame_send(read2, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us
			`spi_frame_begin
				`spi_frame_send(read3, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				if(channel==aborted_channel) begin
					// expect no more data for aborted channel
					read1.expect_symbol_count(2'(channel), 0, 16);
					read2.expect_symbol_count(2'(channel), 0, 0);
					read3.expect_symbol_count(2'(channel), 0, 0);						
					if(transaction_recorder.get_master_tr_count(channel) != 2) begin
						`uvm_error(this.get_type_name(), $sformatf("Master transaction seems not to be aborted, expected only %0d PDCM pulse, got %0d!", 2, transaction_recorder.get_master_tr_count(channel)))
					end
				end
				else begin
					read1.expect_symbol_count(2'(channel), 0, 16);
					read2.expect_symbol_count(2'(channel), 0, 16);
					read3.expect_symbol_count(2'(channel), 0, 16);
					if(transaction_recorder.get_master_tr_count(channel) != 3) begin
						`uvm_error(this.get_type_name(), $sformatf("Unexpected number of PDCM pulses for channel that was not aborted, expected %0d, got %0d!", 3, transaction_recorder.get_master_tr_count(channel)))
					end
				end
			end
			
			enable_dsi_channels(2'b11);
			#50us

			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << aborted_channel; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			if(transaction_recorder.get_master_tr_count(aborted_channel) != 1) begin
				`uvm_error(this.get_type_name(), $sformatf("aborted channel %0d has not been restarted by start PDCM command", aborted_channel))
			end
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end	
	endtask
endclass

