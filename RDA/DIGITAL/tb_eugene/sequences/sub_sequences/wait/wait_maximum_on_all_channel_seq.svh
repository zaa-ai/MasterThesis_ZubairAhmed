class wait_maximum_on_all_channel_seq extends base_wait_seq;
	
	`uvm_object_utils(wait_maximum_on_all_channel_seq) 
    
	function new(string name = "");
		super.new("wait_maximum_on_all_channel");
	endfunction : new

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();
		time start;
		
		log_sim_description("perform maximum DSI wait on all channels", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)	
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#10us;
		
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'h7FFF;)
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		start = $time;
		#(15'h7FFF * 1us + scheme.pdcm_period * 1us);
		#100us;
		expect_wait_time_for_all_channels(0);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			transaction_recorder.expect_tr_count(channel, 1);
			compare_times(32767us, transaction_recorder.get_master_tr_begin_time(channel, 0) - start, $sformatf("DSI wait time at channel %0d", channel), 15us);
		end
		
		transaction_recorder.disable_recorder();
	endtask
endclass

