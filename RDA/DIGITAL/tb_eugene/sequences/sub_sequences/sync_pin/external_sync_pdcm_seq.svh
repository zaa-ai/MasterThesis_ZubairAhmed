class external_sync_pdcm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(external_sync_pdcm_seq) 
	
	function new(string name = "");
		super.new("external_sync_pdcm");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		uvm_reg_data_t tx_shift;
		
		log_sim_description("sync PDCM using SYNCB pin", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 200;
		set_syncb(1'b1);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			set_tdma_scheme_pdcm(i, scheme);
		end
		#50us;
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.read(status, tx_shift);
		
		for(int sync_pdcm = 0; sync_pdcm < 2; sync_pdcm++) begin
			log_sim_description($sformatf("sync CRM using SYNCB pin, SYNC_PDCM = %0d", sync_pdcm), LOG_LEVEL_SEQUENCE);
			
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, sync_pdcm);
			
			expect_SYNC_IDLE_REG(2'b00, 1'b1);
			set_syncb(1'b0);
			#10us;
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
			
			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#300us;
			expect_SYNC_IDLE_REG(2'b00, 1'b0);
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, 0);
				expect_SYNC(i, 2'b11, 1'b1);
			end
			set_syncb(1'b1);
			#100us;
			expect_SYNC_IDLE_REG(2'b11, 1'b1);
			#600us;
			
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				transaction_recorder.expect_tr_count(i, 3);
				expect_SYNC(i, 2'b00, 1'b0);
			end
			check_pdcm_periods(200 * 1us);
			expect_tx_shift(2'b11, 3, tx_shift);
		end
		
		transaction_recorder.disable_recorder();
	endtask
endclass