class crm_dsi_fast_config_access_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_dsi_fast_config_access_seq)
	
	function new(string name = "");
		super.new("crm_dsi_fast_config_access");
	endfunction : new
	
	virtual task run_tests();
		short_filter_at_different_chip_times();
	endtask
	
	task short_filter_at_different_chip_times();
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);
		log_sim_description("use short filter for different chip times", LOG_LEVEL_SEQUENCE);
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CHIPTIME, 2);
		
		while(chip_iterator.has_next()) begin
			int chip_time = chip_iterator.get_current();
			log_sim_description($sformatf("do CRM with configured chiptime of: %0d",  chip_time), LOG_LEVEL_OTHERS);
			chip_iterator.apply_next();
			
			do_and_check_crm(chip_time);
			check_value_at_path(`STRING_OF(`DSI_RX_FILTER_FAST), (chip_time == 2) ? 'b11: 'b00);
		end
		
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
	endtask
	
	task do_and_check_crm(int chip_time);
		dsi3_crm_packet packets[$];
		spi_read_crm_data_packets_seq read_seq;
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_crm_packet next_packet = new();
			if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
			packets.push_back(next_packet);
			add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), chip_time, dsi3_pkg::BITTIME_8US));
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		wait_for_dab(500us, 1'b1);
		#50us;
		`spi_frame_begin
			`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read_seq.expect_flags(2'(channel), packets[channel].crc_correct ? {} : {CRC}); 
			read_seq.expect_packet(2'(channel), packets[channel]);
		end
	endtask
endclass