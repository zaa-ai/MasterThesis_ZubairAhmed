class spi_burst_read_with_wrong_tx_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_burst_read_with_wrong_tx_crc_seq)
	
	function new(string name = "");
		super.new("spi_burst_read_with_wrong_tx_crc");
	endfunction
	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;

		log_sim_description("perform a burst register read and send a wrong MOSI CRC", LOG_LEVEL_SEQUENCE);
		clear_all_irqs();
		// invalidate all TDMA schemes
		`spi_frame_begin
			`spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);)
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;		
		
		`spi_frame_begin
			`spi_frame_send(read_seq, 
				address == 12'(ADDR_INTERRUPT_IRQ_STAT); 
				burst_addresses.size() == 9; 
				burst_addresses[0] == 12'(ADDR_SUPPLY_SUP_IRQ_STAT); 
				burst_addresses[1] == 12'(ADDR_INTERRUPT_ECC_IRQ_STAT);
				burst_addresses[2] == 12'(ADDR_INTERRUPT_ECC_CORR_IRQ_STAT);
				burst_addresses[3] == 12'(ADDR_BUFFER_IRQS_BUF_IRQ_STAT);
				burst_addresses[4] == 12'(ADDR_SPI_SPI_IRQ_STAT);
				burst_addresses[5] == 12'(ADDR_DSI_0_DSI_IRQ_STAT);
				burst_addresses[6] == 12'(ADDR_DSI_1_DSI_IRQ_STAT);
				burst_addresses[7] == 12'(ADDR_DSI_0_DSI_IRQ_MASK);
				burst_addresses[8] == 12'(ADDR_DSI_1_DSI_IRQ_MASK);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b0; )
		`spi_frame_end_with_status({NT0, NT1})
		#10us;
	
		`spi_frame_begin
			`spi_frame_create(spi_read_status_seq, )
		`spi_frame_end_with_status({NT0, NT1,SPICRC})

		clear_all_irqs();
        
		#10us;
	endtask
endclass