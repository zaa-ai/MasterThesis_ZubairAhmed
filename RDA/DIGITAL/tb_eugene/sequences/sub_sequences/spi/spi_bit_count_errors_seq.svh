class spi_bit_count_errors_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_bit_count_errors_seq)
	
	function new(string name = "");
		super.new("spi_bit_count_errors");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("SPI bit errors (too few CRC bits))", LOG_LEVEL_SEQUENCE);
		
		for(int bit_count = 15; bit_count>0; bit_count--) begin
			uvm_reg_data_t value;
			spi_tx_crc_request_seq tx_crc_seq;
			log_sim_description($sformatf("SPI bit errors (too few CRC bits)) - bit count = %1d", bit_count), LOG_LEVEL_OTHERS);

			registers.reset_register(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK);
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hFFFF);
			
			// try to write IRQ_MASK register
			`spi_frame_begin
				`spi_frame_create(spi_write_master_register_seq, address == 12'(ADDR_INTERRUPT_IRQ_MASK); data == 16'h0000;)
				`spi_frame_send(tx_crc_seq, mosi_crc_correct == 1'b1; )
				tx_crc_seq.error_word_index = 1;
				tx_crc_seq.error_word_bit_count = bit_count;
			`spi_frame_end
			#1us;
			
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			
			regmodel.SPI.SPI_registers.SPI_IRQ_STAT.read(status, value);
			
			value = regmodel.SPI.SPI_registers.SPI_IRQ_STAT.ALI_ERR.get();
			if(1'(value) != 1'b1) `uvm_error(this.get_name(), $sformatf("Read unexpected value of SPI_IRQ_STAT.ALI_ERR bit, expected 1, got 0.")) 
			
			value = regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CRC_ERR.get();
			if(1'(value) != 1'b1) `uvm_error(this.get_name(), $sformatf("Read unexpected value of SPI_IRQ_STAT.CRC_ERR bit, expected 1, got 0."))
			
			value = regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_INC.get();
			if(1'(value) != 1'b0) `uvm_error(this.get_name(), $sformatf("Read unexpected value of SPI_IRQ_STAT.CMD_INC bit, expected 0, got 1.")) 
			#50us;
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_end
			#500us;
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
        end
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
        
	endtask
endclass
