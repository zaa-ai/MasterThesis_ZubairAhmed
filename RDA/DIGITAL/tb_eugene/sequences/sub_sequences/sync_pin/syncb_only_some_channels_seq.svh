class syncb_only_some_channels_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(syncb_only_some_channels_seq) 
	
	function new(string name = "");
		super.new("syncb_only_some_channels");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync onyl some channels using SYNCB pin", LOG_LEVEL_SEQUENCE);
		
		transaction_recorder.enable_recorder();
		set_syncb(1'b1);
		
		for(int synced_channels = 'b01; synced_channels <= 'b10; synced_channels = synced_channels << 1) begin
			log_sim_description($sformatf("sync CRM  at channels 0b%2b using SYNCB pin", 2'(synced_channels)), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			expect_SYNC_IDLE_REG(2'b00, 1'b1);
			set_syncb(1'b0);
			#10us;
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
			
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'(synced_channels);)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#300us;
			expect_SYNC_IDLE_REG(2'(~synced_channels), 1'b0);
			
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				if(synced_channels[i] == 1'b1) begin
					transaction_recorder.expect_tr_count(i, 0);
					expect_SYNC(i, 2'(synced_channels), 1'b1);
				end
				else begin
					transaction_recorder.expect_tr_count(i, 1);
					expect_SYNC(i, 2'b00, 1'b0);
				end
			end
			#300us;
			set_syncb(1'b1);
			#20us;
			expect_SYNC_IDLE_REG(2'(synced_channels), 1'b1);
			#450us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, 1);
				expect_SYNC(i, 2'b00, 1'b0);
			end
		end
	endtask
endclass