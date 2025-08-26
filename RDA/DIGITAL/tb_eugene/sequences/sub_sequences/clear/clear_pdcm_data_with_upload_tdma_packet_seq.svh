class clear_pdcm_data_with_upload_tdma_packet_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(clear_pdcm_data_with_upload_tdma_packet_seq) 
	
	function new(string name = "");
		super.new("clear_pdcm_data_with_upload_tdma_packet");
	endfunction
	
	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();

		log_sim_description("clear data of PDCM using TDMA scheme upload", LOG_LEVEL_SEQUENCE);
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				log_sim_description($sformatf("clear PDCM data buffer using TDMA upload on channel %1d", channel), LOG_LEVEL_OTHERS);
				
				`upload_tdma_scheme_with(scheme, channels == 2'b11;)
				
				`spi_frame_begin
					`spi_frame_create(spi_sync_dsi_channels_seq, channel_bits == 2'b11; external_sync == 1'b0;)
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(scheme.pdcm_period * 1us + 100us);
				
				`spi_frame_begin
					`spi_frame_create(spi_upload_tdma_packet_seq, channel_bits == 2'(1<<channel);)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#50us;
				
				for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
					uvm_reg_data_t value;
					regmodel.DSI_PDCM_STAT[i].ring_buffer_registers.BUF_FREE.read(status, value);
					if(i == channel) begin
						if(int'(value) != int'(project_pkg::SIZE_DSI_PDCM_BUF - 1)) begin
							`uvm_error(get_name(), $sformatf("PDCM buffer of channel %0d is expected to be empty, read BUF_FREE: 0x%0h, expected: 0x%0h", i, value, project_pkg::SIZE_DSI_PDCM_BUF - 1))
						end
					end
					else begin
						if(!(int'(value) < int'(project_pkg::SIZE_DSI_PDCM_BUF - 1))) begin
							`uvm_error(get_name(), $sformatf("PDCM buffer of channel %0d is not expected to be empty, read BUF_FREE: 0x%0h, expected any lower value", i, value))
						end
					end
				end
				#100us;
			end
		#100us;
	endtask
endclass