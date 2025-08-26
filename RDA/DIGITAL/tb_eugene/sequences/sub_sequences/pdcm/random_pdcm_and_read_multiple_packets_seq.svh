class random_pdcm_and_read_multiple_packets_seq extends base_dsi_master_seq;
	
	rand logic[7:0] period_count;
	rand dsi3_pkg::sid_length_e source_id;
	rand int symbols_per_packet;
	rand logic[3:0] packet_count;
	
	`uvm_object_utils_begin (random_pdcm_and_read_multiple_packets_seq)
		`uvm_field_int  (period_count, UVM_DEFAULT | UVM_DEC)
		`uvm_field_enum (dsi3_pkg::sid_length_e, source_id, UVM_DEFAULT )
		`uvm_field_int  (symbols_per_packet, UVM_DEFAULT | UVM_DEC )
		`uvm_field_int  (packet_count, UVM_DEFAULT | UVM_DEC )
	`uvm_object_utils_end
	
	constraint co_periods 		{period_count inside {[10:20]};}
	constraint co_packet_count 	{packet_count inside {[1:15]};}
	constraint co_symbols 		{symbols_per_packet inside {[8:50]};}

	function new(string name = "");
		super.new("random_pdcm_and_read_multiple_packets");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description($sformatf("%0d periods of random %0d packets of %0d symbols using SID 0b%02b on all channels", period_count, (int'(packet_count)+1), symbols_per_packet, source_id), LOG_LEVEL_OTHERS);
		
		if(!scheme.randomize() with {packets.size() == int'(packet_count); symbol_count_min == symbols_per_packet; symbol_count_max == symbols_per_packet; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.set_source_id_for_all_packets(source_id);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == period_count;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
		
		repeat(period_count) begin
			#(scheme.pdcm_period * 1us);
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
		#500us;
	endtask
endclass