class spi_incomplete_read_pdcm_with_maximum_size_scheme_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_incomplete_read_pdcm_with_maximum_size_scheme_seq)
	
	function new(string name = "");
		super.new("spi_incomplete_read_pdcm_with_maximum_size_scheme");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("perform incomplete read PDCM commands (too few words) with maximum TDMA scheme on both channels", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 15; symbol_count_min == 255; symbol_count_max == 255; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
			
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd2;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#(scheme.pdcm_period * 1us);
		`spi_frame_begin
			`spi_frame_create(spi_incomplete_read_pdcm_frame_seq, channel_bits == 2'b11; word_count == 5;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#(scheme.pdcm_period * 1us);
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
endclass