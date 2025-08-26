class spi_read_register_and_crm_transmit_with_crc_command_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_read_register_and_crm_transmit_with_crc_command_seq)
	
	function new(string name = "");
		super.new("spi_read_register_and_crm_transmit_with_crc_command");
	endfunction
	
	virtual task run_tests();
		log_sim_description("read register followed by transmit CRM and CRC command", LOG_LEVEL_SEQUENCE);
		clear_all_irqs();
		// invalidate all TDMA schemes
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
		
		`spi_frame_begin
			`spi_frame_create(spi_read_master_register_seq, address == 12'(ADDR_INTERRUPT_IRQ_STAT); burst_addresses.size() == 1; burst_addresses[0] == 12'(ADDR_SUPPLY_SUP_IRQ_STAT);)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_read_master_register_seq, address == 12'(ADDR_INTERRUPT_IRQ_STAT); burst_addresses.size() == 1; burst_addresses[0] == 12'(ADDR_SUPPLY_SUP_IRQ_STAT);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end_with_status({NT0, NT1})
	
		#500us;
	
		`spi_frame_begin
			`spi_frame_create(spi_read_status_seq, )
		`spi_frame_end_with_status({NT0, NT1, CR0, CR1})

		clear_all_irqs();
		#100us;
	endtask
endclass