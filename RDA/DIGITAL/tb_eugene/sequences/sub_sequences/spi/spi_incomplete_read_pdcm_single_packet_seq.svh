class spi_incomplete_read_pdcm_single_packet_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_read_pdcm_single_packet_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_read_pdcm_single_packet");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("perform incomplete read PDCM commands (too few words) with single packet TDMA scheme on each channel", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);

		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			int word_count = spi_read_pdcm_frame_seq::calculate_word_count(2'(channels));
			for (int i = 1; i < word_count; i++) begin
				log_sim_description($sformatf("perform incomplete read PDCM with %0d of %0d words at channels 0b%0b", i, word_count, channels), LOG_LEVEL_OTHERS);
				
				regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
				registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b0);
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'(channels); pulse_count == 8'd2;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(2 * scheme.pdcm_period * 1us);
				`spi_frame_begin
					`spi_frame_create(spi_incomplete_read_pdcm_frame_seq, channel_bits == 2'(channels); word_count == local::i;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#10us;
				registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC, 1'b1);
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'(channels);)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#100us;
			end
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
	endtask

endclass
