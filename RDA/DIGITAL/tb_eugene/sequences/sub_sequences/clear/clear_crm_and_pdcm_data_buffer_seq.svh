class clear_crm_and_pdcm_data_buffer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_crm_and_pdcm_data_buffer_seq) 
	
	function new(string name = "");
		super.new("clear_crm_and_pdcm_data_buffer");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();

		log_sim_description("clear data of CRM and PDCM on all channels", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			spi_read_crm_data_packets_seq read_crm_seq;
			spi_read_pdcm_frame_seq read_pdcm_seq;

			log_sim_description($sformatf("clear CRM and PDCM data buffer on channels 0b%2d", channels), LOG_LEVEL_OTHERS);

			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(450us + scheme.pdcm_period * 1us + 100us);
			
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'(channels); crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;
			
			`spi_frame_begin
				`spi_frame_send(read_crm_seq, channel_bits == 2'b11;)
				`spi_frame_send(read_pdcm_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				read_crm_seq.expect_symbol_count(i, (channels[i] == 1'b1) ? 8'd0 : 8'd8);
				read_pdcm_seq.expect_symbol_count(i, 0, (channels[i] == 1'b1) ? 8'd0 : 8'(scheme.packets[0].symbol_count));
			end
			#100us;
		end
		#100us;
	endtask
endclass