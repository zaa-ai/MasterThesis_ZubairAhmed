class mix_starts_of_crm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(mix_starts_of_crm_seq) 
	
	function new(string name = "");
		super.new("mix_starts_of_crm");
	endfunction

	// FIXME: add some checks

	virtual task run_tests();
		log_sim_description($sformatf("check mixed starts of CRM with shift=%3d", 255), LOG_LEVEL_SEQUENCE);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.write(status, 127);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#1ms;
	endtask
endclass