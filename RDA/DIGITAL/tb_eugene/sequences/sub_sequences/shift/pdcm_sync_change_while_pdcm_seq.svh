class pdcm_sync_change_while_pdcm_seq extends dsi3_sync_base_seq;
	
	rand bit initial_pdcm_sync;
	
	`uvm_object_utils(pdcm_sync_change_while_pdcm_seq) 
	
	function new(string name = "");
		super.new("pdcm_sync_change_while_pdcm");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		int period_count = 3;
		log_sim_description($sformatf("change PDCM sync while pdcm is running"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		apply_tdma_scheme(scheme);
		
		repeat(10) begin	
			int shift = $urandom_range(1, get_max_shift());
			int pdcm_period = scheme.pdcm_period;
			
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM, initial_pdcm_sync);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT, shift);
				
			log_sim_description($sformatf("change PDCM sync from %1b to %1b during running PDCM (period=%0d and shift=%3d)", initial_pdcm_sync, ~initial_pdcm_sync, pdcm_period, shift), LOG_LEVEL_OTHERS);

			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'(period_count);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#((2* pdcm_period/3)*1us + $urandom_range(0, 1000)*1ns);
			
			// change PDCM SYNC
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.SYNC_PDCM.write(status, ~initial_pdcm_sync);
			
			#((period_count*pdcm_period)*1us);
			expect_tx_shift(2'b11, 3, shift, 25ns);
			transaction_recorder.clear_all();
		end
		
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
		transaction_recorder.disable_recorder();
	endtask
endclass