class tdma_scheme_pdcm_with_symbol_noise extends tdma_scheme_pdcm;

	function new(string name = "pdcm_TDMA_scheme_with_symbol_noise");
		super.new(name);
		pdcm_period = 1000;
		chiptime = 3;
		add_packet(tdma_scheme_packet_pdcm::new_packet( 40,  60, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(165, 205, 1, dsi3_pkg::SID_0Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(310, 330, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(435, 475, 2, dsi3_pkg::SID_0Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(580, 600, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(705, 745, 3, dsi3_pkg::SID_0Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(850, 870, 8, dsi3_pkg::SID_8Bit));
		valid = 1'b1;
	endfunction
endclass

class tdma_scheme_pdcm_without_noise extends tdma_scheme_pdcm;

	function new(string name = "pdcm_TDMA_scheme_without_noise");
		super.new(name);
		pdcm_period = 1000;
		chiptime = 3;
		add_packet(tdma_scheme_packet_pdcm::new_packet( 30,  70, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(300, 340, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(570, 610, 8, dsi3_pkg::SID_8Bit));
		add_packet(tdma_scheme_packet_pdcm::new_packet(840, 880, 8, dsi3_pkg::SID_8Bit));
		valid = 1'b1;
	endfunction
endclass


class pdcm_symbol_noise_on_all_channels_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_symbol_noise_on_all_channels_seq)

	function new(string name = "");
		super.new("pdcm_symbol_noise_on_all_channels");
	endfunction : new
	
	task run_tests();
		tdma_scheme_pdcm_with_symbol_noise scheme_with_noise  = new();
		tdma_scheme_pdcm_without_noise scheme_without_noise = new();
		
		log_sim_description("PDCM and symbol noise on all channels", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme_without_noise, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme_with_noise);
		set_tdma_scheme_pdcm(1, scheme_with_noise);
		#50us;
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd3;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#(3 * scheme_without_noise.pdcm_period * 1us);
		
		// read data of all 3 PDCM frames in one SPI frame
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
	endtask
endclass
