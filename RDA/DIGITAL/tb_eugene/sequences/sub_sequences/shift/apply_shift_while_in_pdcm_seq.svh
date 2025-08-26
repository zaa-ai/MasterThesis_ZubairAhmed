class apply_shift_while_in_pdcm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(apply_shift_while_in_pdcm_seq) 
	
	function new(string name = "");
		super.new("apply_shift_while_in_pdcm_seq");
	endfunction

	// FIXME: add some checks

	virtual task run_tests();
		tdma_scheme_pdcm_denso scheme = new();
		log_sim_description("apply shift while doing PDCM", LOG_LEVEL_SEQUENCE);
		
		apply_tdma_scheme(scheme);
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 2;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#0.5ms;
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.write(status, 100);
		
		#2ms;
	endtask
endclass