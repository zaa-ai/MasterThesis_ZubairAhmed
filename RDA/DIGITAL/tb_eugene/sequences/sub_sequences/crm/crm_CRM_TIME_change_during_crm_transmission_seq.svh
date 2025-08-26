class crm_CRM_TIME_change_during_crm_transmission_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_CRM_TIME_change_during_crm_transmission_seq)
	
	function new(string name = "");
		super.new("crm_CRM_TIME_change_during_crm_transmission");
	endfunction
	
	virtual task run_tests();
		log_sim_description($sformatf("change CRM_TIME during CRM transmission"), LOG_LEVEL_SEQUENCE);
		
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
					
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		
		repeat(50) begin
			regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME.write(status, 0);
		end
		
		#200us;
		`spi_frame_begin
			`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)	
		`spi_frame_end

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		#100us;
	endtask
endclass