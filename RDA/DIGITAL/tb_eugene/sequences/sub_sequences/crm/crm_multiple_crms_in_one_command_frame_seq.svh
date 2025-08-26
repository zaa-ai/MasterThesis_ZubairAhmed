class crm_multiple_crms_in_one_command_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_multiple_crms_in_one_command_frame_seq)
	chip_times_iterator_with_register_model chip_iterator;
	
	function new(string name = "");
		super.new("crm_multiple_crms_in_one_command_frame");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("multiple CRM TRANSMIT in one SPI command frame", LOG_LEVEL_SEQUENCE);
		
		chip_iterator = new(regmodel);
		while(chip_iterator.has_next()) begin
			spi_read_crm_data_packets_seq read;
			dsi3_crm_packet packets[project_pkg::DSI_CHANNELS-1:0][$];

			log_sim_description($sformatf("do multiple CRM TRANSMIT in one SPI command frame with chip time of %2dus",  chip_iterator.get_current()), LOG_LEVEL_OTHERS);
		
			repeat(3) begin
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					dsi3_crm_packet next_packet = new();
					if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
					packets[channel].push_back(next_packet);
					add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1),  chip_iterator.get_current(), dsi3_pkg::BITTIME_8US));
				end
			end
			chip_iterator.apply_next();
			
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1500us;
			check_dab(1'b0);
			
			// check results
			for(int packet=0; packet < 3; packet++) begin
				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end				
				
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					read.expect_flags( 2'(channel), packets[channel][packet].crc_correct ? {} : {CRC});
					read.expect_packet(2'(channel), packets[channel][packet]);
				end
			end
			check_dab(1'b1);
			#100us;
		end
		// restore some defaults
		chip_iterator.apply_default();
		#100us;
	endtask
endclass