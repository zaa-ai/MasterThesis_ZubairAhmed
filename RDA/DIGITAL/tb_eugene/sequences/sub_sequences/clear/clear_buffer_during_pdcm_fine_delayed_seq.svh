class clear_buffer_during_pdcm_fine_delayed_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_buffer_during_pdcm_fine_delayed_seq) 
	
	function new(string name = "");
		super.new("clear_buffer_during_pdcm_fine_delayed");
	endfunction
	
	virtual task run_tests();
		log_sim_description("clear data buffer during PDCM reception fine delayed (Issue P52143-488)", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_measure_pdcm_pulse = 1'b0;
		
		run_pdcm_and_clear_buffers(.pdcm_period(500), .symbol_count(32), .max_delay(80));
		run_pdcm_and_clear_buffers(.pdcm_period(100), .symbol_count(4),  .max_delay(70));
	endtask
		
	virtual task run_pdcm_and_clear_buffers(int pdcm_period, int symbol_count, int max_delay);
		tdma_scheme_pdcm scheme_0 = create_scheme(pdcm_period, symbol_count);
		tdma_scheme_pdcm scheme_1 = create_scheme(pdcm_period, symbol_count);
		
		`upload_tdma_scheme_with(scheme_0, channels == 2'b11;)
		
		scheme_0.packets[0].set_start_time_window(30, 30);
		set_tdma_scheme_pdcm(0, scheme_0);
		scheme_1.packets[0].set_start_time_window(30, 30);
		set_tdma_scheme_pdcm(1, scheme_1);
		
		for(int clear_delay = 60; clear_delay <= max_delay; clear_delay++) begin
			log_sim_description($sformatf("clear data buffer during PDCM reception with PDCM period of %0d and %0d symbols per packet at delay of %0dus", pdcm_period, symbol_count, clear_delay), LOG_LEVEL_OTHERS);
			for(int fine_delay = 0; fine_delay < 1000; fine_delay += 50) begin
				clear_buffer_during_pdcm(clear_delay, fine_delay, pdcm_period, symbol_count);
			end
		end
	endtask
	
	function tdma_scheme_pdcm create_scheme(int pdcm_period, int symbol_count);
		tdma_scheme_pdcm scheme = new();
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == symbol_count; symbol_count_max == symbol_count; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = pdcm_period;
		scheme.set_source_id_for_all_packets(dsi3_pkg::SID_8Bit);
		scheme.packets[0].tolerance_int = 1000;
		scheme.packets[0].set_start_time_window(20, 40);
		return scheme;
	endfunction
	
	virtual task clear_buffer_during_pdcm(int clear_delay, int fine_delay, int pdcm_period, int symbol_count);

		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// fist pulse
		wait_for_voltage_edge_at_channel(0, 2ms);
		#50us;
		// second pulse
		wait_for_voltage_edge_at_channel(0, 2ms);
		#50us;
		// third pulse
		wait_for_voltage_edge_at_channel(0, 2ms);
		
		#((clear_delay * 1us) + (fine_delay * 1ns));
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1; crm_buffer == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(pdcm_period * 1us);
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// read again: there must be no more data	
		#50us;
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
	
	virtual task check_ic_status();
		spi_read_status_seq status_seq;	
		`spi_frame_begin
			`spi_frame_send(status_seq, )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		if(status_seq.status.get_value(HE) == 1'b1) `uvm_error(this.get_name(), $sformatf("Unexpected HE status word flag, expected 0 got 1."))
		if(status_seq.status.get_value(BF) == 1'b1) `uvm_error(this.get_name(), $sformatf("Unexpected BF status word flag, expected 0 got 1."))
		if(status_seq.status.get_value(SCI) == 1'b0) `uvm_error(this.get_name(), $sformatf("Unexpected SCI status word flag, expected 1 got 0."))
		if(status_seq.status.get_value(SPICRC) == 1'b1) `uvm_error(this.get_name(), $sformatf("Unexpected SPICRC status word flag, expected 0 got 1."))
	endtask
endclass