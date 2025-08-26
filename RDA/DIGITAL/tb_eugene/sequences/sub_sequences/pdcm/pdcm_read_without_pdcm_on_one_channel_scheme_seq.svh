class pdcm_read_without_pdcm_on_one_channel_scheme_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_read_without_pdcm_on_one_channel_scheme_seq)

	function new(string name = "");
		super.new("pdcm_read_without_pdcm_on_one_channel_scheme");
	endfunction
	
	task run_tests();

		log_sim_description($sformatf("PDCM read data without a valid TDMA scheme on one channel"), LOG_LEVEL_SEQUENCE);

		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			tdma_scheme_pdcm_denso scheme = new();
			log_sim_description($sformatf("read PDCM data with TDMA scheme on channel 0b%0b", channel), LOG_LEVEL_OTHERS);
			
			// invalidate all TDMA schemes
			`spi_frame_begin
				`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#50us;
            for (int channels = 0; channels < project_pkg::DSI_CHANNELS; channels++) begin
                set_tdma_scheme_pdcm(channels, scheme);
            end
			`upload_tdma_scheme_with(scheme, channels == 2'b01 << channel;)
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us);
			
			// check and clear COM_ERR for channel without TDMA scheme
			for (int i=0; i < project_pkg::DSI_CHANNELS; i++) begin
				registers.check_flag(regmodel.DSI[i].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, (channel != i) ? 1'b1 : 1'b0);
				regmodel.DSI[i].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
			end
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
        end
        
	endtask
endclass