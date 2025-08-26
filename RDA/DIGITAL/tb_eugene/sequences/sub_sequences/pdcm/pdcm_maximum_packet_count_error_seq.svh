class pdcm_maximum_packet_count_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_maximum_packet_count_error_seq)

	function new(string name = "");
		super.new("pdcm_maximum_packet_count_error");
	endfunction
	
	task run_tests();
		log_sim_description($sformatf("packet count error with many many more packets in PDCM period"), LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int packet_count = 254; packet_count < 257; packet_count++) begin
			tdma_scheme_pdcm scheme = new();
			
			log_sim_description($sformatf("packet count error with %0d packets per frame", packet_count), LOG_LEVEL_OTHERS);
			
			if(!scheme.randomize() with {packets.size() == packet_count; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			
			// use only 15 packets for upload
			for (int i = 14; i < scheme.packets.size(); i++) scheme.packets[i].enable = 1'b0;
			
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			
			// use many more packets for slave responses
			for (int i = 0; i < scheme.packets.size(); i++) scheme.packets[i].enable = 1'b1;
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			#10us;
			check_dab(1'b1);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
				
			#20us;
			#(scheme.pdcm_period * 1us);
			check_dab(1'b0);
			
			// check FRAME_STAT register
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				int expected_packet_count = packet_count > 255 ? 255 : packet_count;
				// expect PC + count
				registers.check_register(regmodel.DSI[i].DSI3_channel_registers.FRAME_STAT, 16'(16'h8000 + expected_packet_count));
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			check_dab(1'b1);
		end
		#100us;
	endtask
endclass
