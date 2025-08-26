class spi_access_irq_en_wrong_crc_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_access_irq_en_wrong_crc_seq)
	
	function new(string name = "");
		super.new("spi_access_irq_en_wrong_crc");
	endfunction : new
	
	virtual task run_tests();
		spi_write_master_register_seq write_seq;
		spi_read_master_register_seq read_seq;
		logic[15:0] reset_value;

		log_sim_description("write IRQ_MASK register using wrong CRC", LOG_LEVEL_SEQUENCE);
		
		registers.reset_register(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK);
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
		registers.check_flag(regmodel.SPI.SPI_registers.STATUS_WORD.CRC, 1'b0);
		
		`spi_frame_begin
			`spi_frame_send(write_seq, address == 12'(ADDR_INTERRUPT_IRQ_MASK); data == 16'h0000;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b0;)
		`spi_frame_end_with_status({NT0, NT1})
		
		#1us;
		registers.check_flag(regmodel.SPI.SPI_registers.STATUS_WORD.CRC, 1'b1);
		
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 12'(ADDR_INTERRUPT_IRQ_MASK);)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end_with_status({NT0, NT1,SPICRC})
		
		reset_value = 16'(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.get_reset());
		if(read_seq.data != reset_value) `uvm_error(this.get_name(), $sformatf("Read unexpected value from IRQ_MASK register, expected %0h, got %0h.", reset_value, read_seq.data)) 
		
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
        
		#10us;
	endtask
endclass