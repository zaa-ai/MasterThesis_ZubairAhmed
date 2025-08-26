class pdcm_min_max_periods_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_min_max_periods_seq)

	function new(string name = "");
		super.new("pdcm_min_max_periods");
	endfunction : new
    
    parameter   shortint unsigned    period_min = 100;
    parameter   shortint unsigned    period_max = 16'hFFF0;
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("change PDCM period and measure distance between PDCM pulses", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		for(int pdcm_sync = 0; pdcm_sync < 2; pdcm_sync++) begin
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, pdcm_sync);
			
			log_sim_description($sformatf("measure minimal PDCM period, SYNC_PDCM = %0d", pdcm_sync), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			scheme.pdcm_period = 1;
            scheme.packets[0].earliest_start_time = 30;
            scheme.packets[0].latest_start_time = 70;
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
            for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
    			set_tdma_scheme_pdcm(channel, scheme);
            end
			#50us;
            foreach(regmodel.DSI[i])
    			registers.check_register(regmodel.DSI[i].DSI3_channel_registers.PDCM_PERIOD, period_min);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
            
			#(3 * period_min * 1us);
			transaction_recorder.expect_tr_count_for_all_channels(3);
            #100us;
			
			log_sim_description($sformatf("measure maximum PDCM period, SYNC_PDCM = %0d", pdcm_sync), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			scheme.pdcm_period = 'hFFFF;
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
            for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
    			set_tdma_scheme_pdcm(channel, scheme);
            end
			#50us;
            foreach(regmodel.DSI[i])
    			registers.check_register(regmodel.DSI[i].DSI3_channel_registers.PDCM_PERIOD, period_max);

            `spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(3 * period_max * 1us);
			transaction_recorder.expect_tr_count_for_all_channels(3);
            #100us;
		end
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM);
		#100us;
	endtask
	
endclass
