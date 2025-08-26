class syncb_random_commands_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(syncb_random_commands_seq) 
	
	function new(string name = "");
		super.new("syncb_random_commands");
	endfunction
	
	virtual task run_tests();

		log_sim_description("synchronize mixed/random commands", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		// disable sync PDCM feature
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b0);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.write(status, 16'd0);
		
		repeat(30) begin
			string commands;
			int command_count = $urandom_range(2,5);
			int delay = $urandom_range(500,5000);
			time spi_end;
			time syncb_time;
			tdma_scheme_pdcm scheme = new();
			if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				set_tdma_scheme_pdcm(i, scheme);
			end
			
			set_syncb(1'b0);
			#100us;
			
			`spi_frame_begin
				// some random commands
				for(int i=0; i<command_count; i++) begin
					append_random_transmit_commands(frame, commands);
					if(i != command_count-1) commands = $sformatf("%s, ", commands);
				end
				log_sim_description($sformatf("sync %0d random commands (%s) using different SPI frames at all channels", command_count, commands), LOG_LEVEL_OTHERS);
				// sync all channels
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
				// CRM or PDCM on all channels
				randcase
					1 : `spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
					1 : `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				endcase
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			spi_end = $time;
			
			#5ms;
			transaction_recorder.clear_all();
			#(delay * 1us);
			set_syncb(1'b1);
			syncb_time = $time;
			#300us;
			check_channel_sync(2'b11, 2'b11, spi_end);
			
			// check start times
			for (int ch=0; ch < project_pkg::DSI_CHANNELS; ch++) begin
				time start_time = transaction_recorder.get_last_master_tr_begin_time(ch);
				compare_times(syncb_time + 10us, start_time, "expected start after SYNCB activation", 5us);
			end
			#1ms;
		end
		#1ms;
	endtask	
endclass