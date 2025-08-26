class pdcm_shift_sync_channel_1_before_0_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(pdcm_shift_sync_channel_1_before_0_seq) 
	
	function new(string name = "");
		super.new("pdcm_shift_sync_channel_1_before_0");
	endfunction

	virtual task run_tests();
		uvm_reg_data_t tx_shift_value;
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("start channel 1 before channel 0 with SYNC_PDCM = 1", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.read(status, tx_shift_value);
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		apply_tdma_scheme(scheme);
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 3;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#400us;
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 3;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#400us;
			end
			begin
				@(negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
				#30us;
				transaction_recorder.expect_tr_count(0, 0);
				transaction_recorder.expect_tr_count(1, 1);
				expect_tx_shift(2'b10, 1, tx_shift_value);
				transaction_recorder.clear_all();
				
				@(negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
				#30us;
				transaction_recorder.expect_tr_count(0, 1);
				transaction_recorder.expect_tr_count(1, 1);
				expect_tx_shift(2'b11, 1, tx_shift_value);
				transaction_recorder.clear_all();
				
				@(negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
				#30us;
				transaction_recorder.expect_tr_count(0, 1);
				transaction_recorder.expect_tr_count(1, 1);
				expect_tx_shift(2'b11, 1, tx_shift_value);
				transaction_recorder.clear_all();
				
				@(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage);
				#30us;
				transaction_recorder.expect_tr_count(0, 1);
				transaction_recorder.expect_tr_count(1, 0);
				expect_tx_shift(2'b01, 1, tx_shift_value);
				transaction_recorder.clear_all();
			end
		join
		
		#(scheme.pdcm_period * 1us);
		transaction_recorder.disable_recorder();
	endtask
endclass