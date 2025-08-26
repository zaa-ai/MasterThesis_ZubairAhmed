class spi_single_command_ignored_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_single_command_ignored_seq)
	
	function new(string name = "");
		super.new("spi_single_command_ignored");
	endfunction
	
	`define check_cmd_ign(_cmd_)	regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1); \
									registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b0); \
									`spi_frame_begin \
										`spi_frame_create(_cmd_, channel_bits == 2'b00;) \
										`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; ) \
									`spi_frame_end \
									#50us; \
									registers.check_flag(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN, 1'b1); \
									#100us;
	
	virtual task run_tests();
		log_sim_description("SPI command ignored error for single commands", LOG_LEVEL_SEQUENCE);
		clear_all_irqs();
		
		`check_cmd_ign(spi_crm_seq)
		`check_cmd_ign(spi_pdcm_seq)
		`check_cmd_ign(spi_discovery_mode_seq)
		`check_cmd_ign(spi_upload_tdma_packet_seq)
		`check_cmd_ign(spi_validate_tdma_scheme_seq)
		`check_cmd_ign(spi_read_crm_data_packets_seq)
		`check_cmd_ign(spi_read_pdcm_frame_seq)
		`check_cmd_ign(spi_dsi_wait_seq)
		`check_cmd_ign(spi_sync_dsi_channels_seq)
		`check_cmd_ign(spi_clear_dsi_command_queue_seq)
		`check_cmd_ign(spi_clear_dsi_data_buffers_seq)
		`check_cmd_ign(spi_measure_quiescent_current_seq)
		
		clear_all_irqs();
	endtask
endclass
