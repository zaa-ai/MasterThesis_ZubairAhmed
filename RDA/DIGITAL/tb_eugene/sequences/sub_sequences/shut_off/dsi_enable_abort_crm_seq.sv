class dsi_enable_abort_crm_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_enable_abort_crm_seq) 
    
	function new(string name = "");
		super.new("dsi_enable_abort_crm");
	endfunction

	virtual task run_tests();
		transaction_recorder.enable_recorder();
		
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
        
		for (int aborted_channel=0; aborted_channel < project_pkg::DSI_CHANNELS; aborted_channel++) begin
			spi_read_crm_data_packets_seq read1, read2;
			spi_crm_seq crm_seq;
			dsi3_crm_packet packets[project_pkg::DSI_CHANNELS-1:0][$];
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				// add only one packet for the aborted channel
				create_random_crm_packets(channel, (channel == aborted_channel) ? 1 : 2, packets);
			end
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			
			disable_dsi_channels(2'b01 << aborted_channel);
			#500us;

			`spi_frame_begin
				`spi_frame_send(read1, channel_bits == 2'b11;)
				`spi_frame_send(read2, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			// check results
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				read1.expect_flags( 2'(channel), packets[channel][0].crc_correct ? {} : {CRC});
				read1.expect_packet(2'(channel), packets[channel][0]);
				
				if(channel==aborted_channel) begin
					// expect no second packet for aborted channel
					read2.expect_flags(			2'(channel), {});
					read2.expect_symbol_count(	2'(channel), 8'd0);
					read2.expect_packet_data(	2'(channel), 0, 16'h0000);
					read2.expect_packet_data(	2'(channel), 1, 16'h0000);						
					
					if(transaction_recorder.get_last_master_tr(channel).data.size() >= 32) begin
						`uvm_error(this.get_type_name(), $sformatf("Master transaction seems not to be aborted, expected less than %0d bits, got %0d!", 32, transaction_recorder.get_last_master_tr(channel).data.size()))
					end
				end
				else begin
					read2.expect_flags( 2'(channel), packets[channel][1].crc_correct ? {} : {CRC});
					read2.expect_packet(2'(channel), packets[channel][1]);
				end
				// check master transmission
				if(transaction_recorder.get_master_tr_count(channel) != 2) begin
					`uvm_error(this.get_type_name(), $sformatf("Unexpected number of master transactions for channel that was not aborted, expected %0d, got %0d!", 2, transaction_recorder.get_master_tr_count(channel)))
				end
			end
			
			#500us;
			
			enable_dsi_channels(2'b11);

			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_send(crm_seq, channel_bits == 2'b01 << aborted_channel; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#300us;
			transaction_recorder.expect_packets(aborted_channel, {crm_seq.crm_packet});
			#200us;
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#100us;
		end
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b1;
	endtask
	
	function void create_random_crm_packets(int channel, int packet_count, ref dsi3_crm_packet packets[project_pkg::DSI_CHANNELS-1:0][$]);
		packets[channel].delete();
		repeat(packet_count) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets[channel].push_back(next_packet);
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1)));
		end
	endfunction
endclass