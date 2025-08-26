class start_pdcm_without_valid_tdma_scheme_seq extends base_upload_tdma_schemes_seq;

	`uvm_object_utils(start_pdcm_without_valid_tdma_scheme_seq)
	
	function new(string name = "");
		super.new("start_pdcm_without_valid_tdma_scheme");
	endfunction
	
	virtual task run_tests();

		log_sim_description("start PDCM without valid TDMA scheme", LOG_LEVEL_SEQUENCE);
		
		// invalidate any existing TDMA scheme
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		clear_COM_ERR_irqs();
		
		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			transaction_recorder.enable_recorder();
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == channels[project_pkg::DSI_CHANNELS-1:0];)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#100us;
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR, channels[channel] == 1'b1);
				if(channels[channel] == 1'b1) begin
					transaction_recorder.expect_tr_count_for_all_channels(0);
				end
			end
			clear_COM_ERR_irqs();
			#10us;
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
	endtask
	
	// clear any existing PDCM_ERR IRQ
	task clear_COM_ERR_irqs();
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.COM_ERR.write(status, 1'b1);
		end
	endtask
	
endclass