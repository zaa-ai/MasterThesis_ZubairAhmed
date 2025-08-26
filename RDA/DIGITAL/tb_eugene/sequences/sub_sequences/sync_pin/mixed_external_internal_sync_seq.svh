class mixed_external_internal_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(mixed_external_internal_sync_seq) 
	
	function new(string name = "");
		super.new("mixed_external_internal_sync");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync some channels using SYNCB pin and some using internal sync", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		set_syncb(1'b1);
		
		for(int synced_channels = 'b01; synced_channels <= 'b10; synced_channels = synced_channels << 1) begin
			logic[project_pkg::DSI_CHANNELS-1:0] waiting_channel = one_of(2'(~synced_channels));
			
			log_sim_description($sformatf("sync channels 0b%2b using SYNCB pin and channels 0b%2b using internal sync", 2'(synced_channels), 2'(~synced_channels)), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			expect_SYNC_IDLE_REG(2'b00, 1'b1);
			set_syncb(1'b0);
			#10us;
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_dsi_wait_seq, channel_bits == waiting_channel; wait_time == 15'd300;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'(synced_channels);)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'(~synced_channels);)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			fork
				begin
					#100us;
					expect_SYNC_IDLE_REG(waiting_channel, 1'b0);
					for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
						transaction_recorder.expect_tr_count(i, 0);
						if(synced_channels[i] == 1'b1) begin
							expect_SYNC(i, 2'(synced_channels), 1'b1);
						end
						else if(waiting_channel[i] == 1'b1) begin
							expect_SYNC(i, 2'b00, 1'b0);
						end
						else begin
							expect_SYNC(i, 2'(~synced_channels), 1'b0);
						end
					end
				end
				begin
					#450us;
					expect_SYNC_IDLE_REG(2'(~synced_channels), 1'b0);
					for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
						transaction_recorder.expect_tr_count(i, 0);
					end
				end
				begin
					#900us;
					for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
						transaction_recorder.expect_tr_count(i, (synced_channels[i] == 1'b1) ? 0 : 1);
						if(synced_channels[i] == 1'b1) begin
							expect_SYNC(i, 2'(synced_channels), 1'b1);
						end
						else begin
							expect_SYNC(i, 2'b00, 1'b0);
						end
					end
					
				end
				begin
					#1000us;
					set_syncb(1'b1);
				end
				begin
					#1020us;
					expect_SYNC_IDLE_REG(2'(synced_channels), 1'b1);
				end
				begin
					#1500us;
					for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
						transaction_recorder.expect_tr_count(i, 1);
						expect_SYNC(i, 2'b00, 1'b0);
					end
				end
			join
		end
		transaction_recorder.disable_recorder();
	endtask
	
	function logic[project_pkg::DSI_CHANNELS-1:0] one_of(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		logic[project_pkg::DSI_CHANNELS-1:0] one_channel = 2'b00;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			if(channels[i] == 1'b1) begin
				one_channel[i] = 1'b1;
				break;
			end
		end
		return one_channel;
	endfunction
endclass