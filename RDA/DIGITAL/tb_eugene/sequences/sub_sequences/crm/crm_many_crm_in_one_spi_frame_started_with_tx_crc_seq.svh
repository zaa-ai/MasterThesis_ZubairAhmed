class crm_many_crm_in_one_spi_frame_started_with_tx_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_many_crm_in_one_spi_frame_started_with_tx_crc_seq)
	
	function new(string name = "");
		super.new("crm_many_crm_in_one_spi_frame_started_with_tx_crc");
	endfunction : new
	
	virtual task run_tests();
		int outer = 3;
		int inner = 5;
		log_sim_description("Many CRMs in one SPI frame started with TX CRCs", LOG_LEVEL_SEQUENCE);
		
		transaction_recorder.clear_all();
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR, 16'd300);
		create_CRM_packets_without_data(.packet_count(outer * inner), .channels(2'b11));
		
		`spi_frame_begin
			repeat(outer) begin
				repeat (inner) begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b1;)
					`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'd10;)
				end
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			end
		`spi_frame_end
	
		#(outer * inner * (300us + 10us)); 
		transaction_recorder.expect_tr_count_for_all_channels(inner * outer);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR);
	endtask
endclass