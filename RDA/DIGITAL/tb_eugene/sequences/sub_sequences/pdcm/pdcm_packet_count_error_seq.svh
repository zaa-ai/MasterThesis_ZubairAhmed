class pdcm_packet_count_error_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_packet_count_error_seq)

	function new(string name = "");
		super.new("pdcm_packet_count_error");
	endfunction
	
	task run_tests();
		log_sim_description($sformatf("packet count error for all TDMA packet counts"), LOG_LEVEL_SEQUENCE);
		
		for (int packet_count = 1; packet_count < 16; packet_count++) begin
			tdma_scheme_pdcm scheme = new();
			tdma_scheme_packet_pdcm additional_packet;
			int additional_packet_start;
			
			log_sim_description($sformatf("packet count error for TDMA scheme with %0d packets", packet_count), LOG_LEVEL_OTHERS);
			
			if(!scheme.randomize() with {packets.size() == packet_count; symbol_count_min == 4; symbol_count_max == 4; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			scheme.pdcm_period = scheme.pdcm_period + 100;
			
			`upload_tdma_scheme_with(scheme, channels == 2'b11;)
			set_tdma_scheme_pdcm(0, scheme);
			set_tdma_scheme_pdcm(1, scheme);
			
			`spi_frame_begin
				`spi_frame_create(spi_sync_dsi_channels_seq, channel_bits == 2'b11; external_sync == 1'b0;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
				
			#20us;
			#(scheme.pdcm_period * 1us);
			
			// add an additional packet
			additional_packet_start = scheme.packets[$].calculate_endtime_of_packet(3) + 30;
			additional_packet = tdma_scheme_packet_pdcm::new_packet(additional_packet_start, additional_packet_start, 4, dsi3_pkg::SID_0Bit);			
			scheme.add_packet(additional_packet);
			
			#(scheme.pdcm_period * 1us);
			
			// remove additional packet
			scheme.packets.pop_back();
			
			#(scheme.pdcm_period * 1us);

			// check FRAME_STAT register
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				registers.check_register(regmodel.DSI[i].DSI3_channel_registers.FRAME_STAT, 16'(packet_count));
			end
		
			// read data of all 3 PDCM frames in one SPI frame
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end
	endtask
endclass
