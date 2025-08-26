class pdcm_shift_sync_with_register_writes_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(pdcm_shift_sync_with_register_writes_seq) 
	
	function new(string name = "");
		super.new("pdcm_shift_sync_with_register_writes");
	endfunction

	/**
	 * - start PDCM on channel 1
	 * - perform some register writes
	 * - start PDCM on channel 0, this channel has to wait until next PDCM pulse of channel 1
	 */
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description("start channel 1 before channel 0 with SYNC_PDCM = 1 and many register writes", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, 1);
		
		for (int tx_shift = 0; tx_shift <= 36; tx_shift++) begin
			
			log_sim_description($sformatf("start synced PDCM with TX_SHIFT of %0d", tx_shift), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, tx_shift);
			
			if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			apply_tdma_scheme(scheme);
			
			fork
				begin
					`spi_frame_begin
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b10; pulse_count == 3;)
						repeat(10) begin
							`spi_frame_create(spi_write_master_register_seq, address==12'(ADDR_INTERRUPT_IRQ_MASK); data==16'hffff;)
						end
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 3;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					#400us;
				end
				begin
					#60us;
					transaction_recorder.expect_tr_count(0, 0);
					transaction_recorder.expect_tr_count(1, 1);
					transaction_recorder.clear_all();
					
					#(scheme.pdcm_period * 1us);
					transaction_recorder.expect_tr_count(0, 1);
					transaction_recorder.expect_tr_count(1, 1);
					expect_tx_shift(2'b11, 1, tx_shift);
					transaction_recorder.clear_all();
					
					#(scheme.pdcm_period * 1us);
					transaction_recorder.expect_tr_count(0, 1);
					transaction_recorder.expect_tr_count(1, 1);
					expect_tx_shift(2'b11, 1, tx_shift);
					transaction_recorder.clear_all();
					
					#(scheme.pdcm_period * 1us);
					transaction_recorder.expect_tr_count(0, 1);
					transaction_recorder.expect_tr_count(1, 0);
					transaction_recorder.clear_all();
				end
			join
			#(scheme.pdcm_period * 1us);
		end
		
		transaction_recorder.disable_recorder();
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
	endtask
endclass