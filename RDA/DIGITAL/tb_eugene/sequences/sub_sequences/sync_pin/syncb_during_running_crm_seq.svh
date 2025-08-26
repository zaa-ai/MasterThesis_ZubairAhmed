class syncb_during_running_crm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(syncb_during_running_crm_seq) 
	
	function new(string name = "");
		super.new("syncb_during_running_crm");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync CRM using SYNCB pin during an already running CRM", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_syncb(1'b0);
			#100us;
			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#300us;
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, (i == channel) ? 1 : 0);
			end
			set_syncb(1'b1);
			#450us;
			// check start times
			begin
				time first_start_time = transaction_recorder.get_last_master_tr_begin_time(0);
				for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
					transaction_recorder.expect_tr_count(i, (i == channel) ? 2 : 1);
					if(i > 0) begin
						time start_time = transaction_recorder.get_last_master_tr_begin_time(i);
						compare_times(first_start_time, start_time, "expected start after SYNCB activation", 2us);
					end
				end
			end
			#300us;
		end
		transaction_recorder.disable_recorder();
	endtask
endclass