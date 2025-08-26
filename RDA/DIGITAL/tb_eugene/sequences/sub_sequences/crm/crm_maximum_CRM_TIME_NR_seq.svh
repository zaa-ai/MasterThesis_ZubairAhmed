class crm_maximum_CRM_TIME_NR_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_maximum_CRM_TIME_NR_seq)
	
	function new(string name = "");
		super.new("crm_maximum_CRM_TIME_NR");
	endfunction
	
	virtual task run_tests();
		int crm_time_nr = 'h7FF;
		log_sim_description($sformatf("CRM without expected response and maximum CRM_TIME_NR setting"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR, 16'(crm_time_nr));
					
			log_sim_description($sformatf("CRM with a bit time of %s and CRM_TIME = %0d", bit_time.name(), crm_time_nr), LOG_LEVEL_OTHERS);
			transaction_recorder.clear_all();
			
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(3 * crm_time_nr * 1us);
			#300us;
			transaction_recorder.expect_tr_count_for_all_channels(3);
		end

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		transaction_recorder.disable_recorder();
	endtask
endclass