class pdcm_read_empty_data_seq extends base_dsi_master_seq;
	
	rand logic[project_pkg::DSI_CHANNELS-1:0] active_channels;
	
	`uvm_object_utils_begin (pdcm_read_empty_data_seq)
		`uvm_field_int (active_channels, UVM_DEFAULT | UVM_BIN )
	`uvm_object_utils_end

	function new(string name = "");
		super.new("pdcm_read_empty_data");
	endfunction
	
	task run_tests();
		tdma_scheme_pdcm scheme = new();
		spi_read_pdcm_frame_seq read_seq;

		// clear PDCM data from buffer
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end

		if(!scheme.randomize() with {packets.size() > 0; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		log_sim_description($sformatf("Read empty PDCM data with a TDMA scheme of %0d packets on channels 0b%02b", scheme.packets.size(), active_channels), LOG_LEVEL_OTHERS);

		`upload_tdma_scheme_with(scheme, channels == active_channels;)
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(active_channels[channel]) begin
				set_tdma_scheme_pdcm(channel, scheme);
			end
		end
		#50us;

		`spi_frame_begin
			`spi_frame_send(read_seq, channel_bits == active_channels;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(read_seq.channel_bits[channel]) begin
				for (int packet_index=0; packet_index < scheme.packets.size(); packet_index++) begin
					// check flags
					read_seq.expect_flags(channel, packet_index, {});
					// check symbol count
					read_seq.expect_symbol_count(channel, packet_index, 8'd0);
					// check read data
					read_seq.expect_empty(channel, packet_index);
				end
			end
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
		#100us;
	endtask
	
endclass