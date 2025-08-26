class pdcm_late_single_packet_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_late_single_packet_seq)

	function new(string name = "");
		super.new("pdcm_late_single_packet");
	endfunction : new
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		spi_read_pdcm_frame_seq read_seq;

		log_sim_description($sformatf("PDCM with a single (and sometimes late) packet"), LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 300;
		scheme.packets[0].set_start_time_window(30, 70);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for(int delay = 80; delay < 200; delay += 10) begin
		
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#20us;
			#(scheme.pdcm_period * 1us);
			scheme.packets[0].set_start_time_window(delay, delay);
			#(scheme.pdcm_period * 1us);
			scheme.packets[0].set_start_time_window(30, 70);
			#(scheme.pdcm_period * 1us);
			// read data of all 3 PDCM frames in one SPI frame
			`spi_frame_begin
				`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
	endtask
endclass
