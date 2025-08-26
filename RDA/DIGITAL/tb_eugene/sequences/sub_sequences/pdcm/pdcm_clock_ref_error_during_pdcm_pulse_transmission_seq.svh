class pdcm_clock_ref_error_during_pdcm_pulse_transmission_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_clock_ref_error_during_pdcm_pulse_transmission_seq)

	function new(string name = "");
		super.new("pdcm_clock_ref_error_during_pdcm_pulse_transmission");
	endfunction : new
	
	task run_tests();
		int frequency = 500_000;
		tdma_scheme_pdcm scheme = new();
		log_sim_description("clock error during transmission of PDCM pulse", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 2; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[1] = {};
		get_checker_config().enable_hardware_error_check = 1'b0;
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		#50us;

		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			log_sim_description($sformatf("clock error during transmission of PDCM pulse at channel %0d", channel), LOG_LEVEL_OTHERS);
			
			get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[channel] = {0};
			
			set_clk_ref(frequency * 0.75);
			#10us;
			set_clk_ref(frequency);
			#180us;
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end_with_status({HE})
			
			#(scheme.pdcm_period * 1us);

			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[0] = {};
		get_checker_config().expect_PDCM_clock_ref_error_in_dsi_packet[1] = {};
		get_checker_config().enable_hardware_error_check = 1'b1;
		#500us;
	endtask
endclass
