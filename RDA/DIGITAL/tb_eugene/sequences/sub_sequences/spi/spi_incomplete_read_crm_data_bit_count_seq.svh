class spi_incomplete_read_crm_data_bit_count_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_read_crm_data_bit_count_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_read_crm_data_bit_count");
	endfunction
	
	virtual task run_tests();
		log_sim_description("perform incomplete read CRM commands (too few words and too few bits) on each channel", LOG_LEVEL_SEQUENCE);

		for (int channels=1; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			spi_incomplete_read_crm_data_packets_seq inc_read_seq;
			int expected_word_count = spi_read_crm_data_packets_seq::calculate_word_count(2'(channels));
			
			log_sim_description($sformatf("perform incomplete read CRM data with %0d of %0d words and only 8 bits in last word at channel 0b%0b", expected_word_count-1, expected_word_count, channels), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;				
			
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.ALI_ERR, 1'b0);
			
			check_dab(1'b1);
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'(channels); broad_cast == 1'b0;)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'(channels); broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
			check_dab(1'b0);
			`spi_frame_begin
				`spi_frame_send(inc_read_seq, channel_bits == 2'(channels); word_count == expected_word_count-1;)
				inc_read_seq.error_word_index = expected_word_count-2;
				inc_read_seq.error_word_bit_count = 8;
			`spi_frame_end
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			#20us;
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b1);
			registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.ALI_ERR, 1'b1);
			check_dab(1'b0);
			#20us;
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'(channels); )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;
			check_dab(1'b1);
			#50us;
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
	endtask
endclass