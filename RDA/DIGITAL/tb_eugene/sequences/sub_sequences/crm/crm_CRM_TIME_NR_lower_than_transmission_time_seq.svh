class crm_CRM_TIME_NR_lower_than_transmission_time_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_CRM_TIME_NR_lower_than_transmission_time_seq)
	
	function new(string name = "");
		super.new("crm_CRM_TIME_NR_lower_than_transmission_time");
	endfunction
	
	virtual task run_tests();
		log_sim_description($sformatf("CRM without expected response and a minimum CRM_TIME_NR setting"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		for (dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			int crm_transmission_duration = 256 * dsi3_pkg::get_bit_time_factor(bit_time);
			registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
			
			for (int crm_time_nr = 0; crm_time_nr < crm_transmission_duration; crm_time_nr += 50) begin
				log_sim_description($sformatf("CRM with a bit time of %s and CRM_TIME_NR = %0d", bit_time.name(), crm_time_nr), LOG_LEVEL_OTHERS);
				registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR, crm_time_nr);
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
				
				#(3 * crm_transmission_duration * 1us);
				#300us;
				transaction_recorder.expect_tr_count_for_all_channels(3);
			end
		end

		// restore some defaults
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME_NR);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
		transaction_recorder.disable_recorder();
	endtask
endclass