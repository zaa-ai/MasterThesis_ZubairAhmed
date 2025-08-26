class pdcm_chip_noise_on_all_channels_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_chip_noise_on_all_channels_seq)

	function new(string name = "");
		super.new("pdcm_chip_noise_on_all_channels");
	endfunction : new
	
	task run_tests();
		logic[7:0] pdcm_periods = 8'h3;
		tdma_scheme_pdcm_without_noise scheme_without_noise = new();
		
		log_sim_description("PDCM and chip noise on all channels", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(scheme_without_noise, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme_without_noise);
		set_tdma_scheme_pdcm(1, scheme_without_noise);
		#50us;
		
		for(int chips_per_symbol=1; chips_per_symbol < 3; chips_per_symbol++) begin
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == pdcm_periods;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			fork
				disturb_channel(0, pdcm_periods, chips_per_symbol);
				disturb_channel(1, pdcm_periods, chips_per_symbol);
				#(3 * scheme_without_noise.pdcm_period * 1us);
			join
			
			// read data of all 3 PDCM frames in one SPI frame
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end
	endtask
	
	task disturb_channel(int channel, logic[7:0] pdcm_periods, int chips_per_symbol);
		dsi3_master_config cfg = get_dsi3_master_config(channel);
		repeat(pdcm_periods) begin
			@(negedge cfg.vif.cable.Voltage)
			fork
				begin
					#($urandom_range(165, 270) * 1us);
					send_chip_disturbance(channel, chips_per_symbol);
				end
				begin
					#($urandom_range(435, 540) * 1us);
					send_chip_disturbance(channel, chips_per_symbol);
				end
				begin
					#($urandom_range(705, 810) * 1us);
					send_chip_disturbance(channel, chips_per_symbol);
				end
			join
		end
	endtask
	
	task send_chip_disturbance(int channel, int chips_per_symbol);
		dsi3_slave_tr disturbance;
		dsi3_slave_sequencer_t seq = get_slave_agent(channel).m_sequencer;
		`uvm_do_on_with(disturbance, seq, {
				msg_type == dsi3_pkg::CRM; 
				data.size() == 1;
				chips_per_symbol == local::chips_per_symbol; 
				chiptime == 3; 
				data[0] inside {4'h1, 4'h5, 4'h6, 4'hA, 4'hB, 4'hF}; // use some symbols without '0' chips
				symbol_coding_error_injection == NEVER_ERROR;})
	endtask
endclass
