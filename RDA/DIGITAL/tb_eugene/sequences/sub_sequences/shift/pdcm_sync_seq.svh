class pdcm_sync_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(pdcm_sync_seq) 
	
	function new(string name = "");
		super.new("pdcm_sync");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("sync PDCM with SYNC_PDCM == 0", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		apply_tdma_scheme(scheme);
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b0);
		
		for(int channel_index = 0; channel_index < project_pkg::DSI_CHANNELS; channel_index++) begin
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'(1<<channel_index); pulse_count == 10;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#400us;
		end
		#(12 * scheme.pdcm_period * 1us);
		begin
			time start0, start1;
			check_pdcm_pulse_count(10);
			start0 = transaction_recorder.get_master_tr_begin_time(0, 0);
			start1 = transaction_recorder.get_master_tr_begin_time(1, 0);
			compare_times(400us, start1-start0, $sformatf("start time difference of first PDCM pulse on channel 0 and 1"), 10us);
		end
		transaction_recorder.clear_all();
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, 1'b1);
		
		for (int start_channel=0; start_channel<project_pkg::DSI_CHANNELS; start_channel++) begin
			log_sim_description($sformatf("sync PDCM: enabled | start channel = %1d", start_channel), LOG_LEVEL_SEQUENCE);
			for(int channel_index = start_channel; channel_index < project_pkg::DSI_CHANNELS; channel_index++) begin
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'(1<<channel_index); pulse_count == 3;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#400us;
			end
			#(4 * scheme.pdcm_period * 1us);
			transaction_recorder.clear_all();
		end
		transaction_recorder.disable_recorder();
	endtask
endclass