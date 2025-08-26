class clear_pdcm_data_with_tdma_scheme_upload_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_pdcm_data_with_tdma_scheme_upload_seq) 
	
	function new(string name = "");
		super.new("clear_pdcm_data_with_tdma_scheme_upload");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();

		log_sim_description("clear data of PDCM using TDMA scheme upload", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				spi_read_pdcm_frame_seq read_seq;
	
				log_sim_description($sformatf("clear PDCM data buffer using TDMA upload on channel %1d", channel), LOG_LEVEL_OTHERS);
	
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(scheme.pdcm_period * 1us + 100us);
				
				`upload_tdma_scheme_with(scheme, channels == 2'(1<<channel);)
				#50us;
				
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
					read_seq.expect_symbol_count(i, 0, (i == channel) ? 0 : scheme.packets[0].symbol_count);
				end
				#100us;
			end
		#100us;
	endtask
endclass