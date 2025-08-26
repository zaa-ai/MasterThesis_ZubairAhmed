class single_pdcm_on_single_channel_seq extends base_dsi_master_seq;

	`uvm_object_utils(single_pdcm_on_single_channel_seq)
	
	function new(string name = "");
		super.new("single_pdcm_on_single_channel");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("single PDCM on single channel", LOG_LEVEL_SEQUENCE);

		for(int channel_index = 0; channel_index < project_pkg::DSI_CHANNELS ; channel_index++) begin
			tdma_scheme_pdcm scheme = new();
			if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
			
			`upload_tdma_scheme_with(scheme, channels == 2'b01 << channel_index;)
			set_tdma_scheme_pdcm(channel_index, scheme);
	
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel_index; pulse_count == 1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#(scheme.pdcm_period * 1us);
	
			repeat(2) begin
				spi_read_pdcm_frame_seq read_seq;
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b01 << channel_index;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#10us;
			end
			#100us;
		end
	endtask
endclass
