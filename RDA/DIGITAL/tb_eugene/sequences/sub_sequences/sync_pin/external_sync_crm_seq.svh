class external_sync_crm_seq extends dsi3_sync_base_seq;
	
	`uvm_object_utils(external_sync_crm_seq) 
	
	function new(string name = "");
		super.new("external_sync_crm");
	endfunction
	
	virtual task run_tests();
		log_sim_description("sync CRM using SYNCB pin", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		set_syncb(1'b0);
		#10us;
		expect_SYNC_IDLE_REG(4'b0000, 1'b0);
		
		transaction_recorder.clear_all();
		`spi_frame_begin
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
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
		#400us;
		for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
			transaction_recorder.expect_tr_count(i, 1);
			expect_SYNC(i, 2'b00, 1'b0);
		end
		
		transaction_recorder.disable_recorder();
	endtask
endclass