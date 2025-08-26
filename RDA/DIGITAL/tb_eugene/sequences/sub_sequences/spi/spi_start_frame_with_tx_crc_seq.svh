class spi_start_frame_with_tx_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_start_frame_with_tx_crc_seq)
	
	function new(string name = "");
		super.new("spi_start_frame_with_tx_crc");
	endfunction : new
	
	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		spi_tx_crc_request_seq tx_crc_seq;

		log_sim_description("frame starts with TX_CRC command", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_send(tx_crc_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end
		
		if(tx_crc_seq.miso_crc != crc_calculation_pkg::spi_calculate_correct_crc({tx_crc_seq.data_out[0]})) `uvm_error(this.get_name(), $sformatf("Unexpected MISO CRC at beginning of frame, expected %0h, got %0h.", crc_calculation_pkg::spi_calculate_correct_crc({16'h0000}), tx_crc_seq.miso_crc))
		
		#500us;
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
		`spi_frame_end_with_status({NT0, NT1, CR0, CR1})
		
		read.expect_symbol_count(0,  8'd8);
		read.expect_symbol_count(1,  8'd8);
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
        
		#10us;
	endtask
endclass