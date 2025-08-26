class random_pdcm_fill_data_buffer_seq extends base_dsi_master_seq;
	
	rand int symbols_per_packet;
	
	`uvm_object_utils_begin (random_pdcm_fill_data_buffer_seq)
		`uvm_field_int(symbols_per_packet, UVM_DEFAULT | UVM_DEC )
	`uvm_object_utils_end
	
	constraint co_symbols {symbols_per_packet inside {[64:255]};}
	
	function new(string name = "");
		super.new("random_pdcm_fill_data_buffer");
	endfunction 
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		logic[7:0] period_count = 8'h0; // number of periods
		int unsigned extra_periods;
		int unsigned max_period_length = 0; // max PDCM period length
		int unsigned buffer_words = 0; // words already contained in data buffer

		log_sim_description($sformatf("fill DSI data buffers with random data of %0d symbols per period on all channels", symbols_per_packet), LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == symbols_per_packet; symbol_count_max == symbols_per_packet; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		
		// fill the buffer
		while(buffer_words <= int'(project_pkg::SIZE_DSI_PDCM_BUF)) begin
			buffer_words += scheme.packets[0].get_word_count_of_data();
			buffer_words++; // 1 word for frame header
			buffer_words++; // 1 word for packet status
			period_count += 8'b1;
		end
		
		extra_periods = $urandom_range(1,5); // some extra periods
		period_count += 8'(extra_periods); 
		
		if(get_bfwb() != 1'b1) `uvm_error(this.get_type_name(), $sformatf("Unexpected BFWB pin level, expected 1, got %0b", get_bfwb()))
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == period_count;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(scheme.pdcm_period * (period_count+1) * 1us);
		if(get_bfwb() != 1'b0) `uvm_error(this.get_type_name(), $sformatf("Unexpected BFWB pin level, expected 0, got %0b", get_bfwb()))
		
		repeat(period_count) begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				`spi_frame_begin
					`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'(1 << channel);)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
		end
		if(get_bfwb() != 1'b1) `uvm_error(this.get_type_name(), $sformatf("Unexpected BFWB pin level, expected 1, got %0b", get_bfwb()))
	endtask
	
endclass