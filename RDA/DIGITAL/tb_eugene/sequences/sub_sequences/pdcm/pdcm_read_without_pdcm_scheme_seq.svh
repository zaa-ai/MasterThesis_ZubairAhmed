class pdcm_read_without_pdcm_scheme_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_read_without_pdcm_scheme_seq)

	function new(string name = "");
		super.new("pdcm_read_without_pdcm_scheme");
	endfunction
	
	task run_tests();

		log_sim_description($sformatf("do a PDCM read data without a valid TDMA scheme"), LOG_LEVEL_SEQUENCE);

		// invalidate all TDMA schemes
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#50us;

		for (int channels=0; channels < 2 ** project_pkg::DSI_CHANNELS; channels++) begin
			log_sim_description($sformatf("read PDCM data without valid TDMA scheme for channels 0b%0b", channels), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'(channels);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#50us;
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
		#100us;
	endtask
endclass