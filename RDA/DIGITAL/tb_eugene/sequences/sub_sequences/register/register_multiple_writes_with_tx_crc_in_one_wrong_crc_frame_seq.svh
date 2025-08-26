class register_multiple_writes_with_tx_crc_in_one_wrong_crc_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_multiple_writes_with_tx_crc_in_one_wrong_crc_frame_seq)
	
	function new(string name = "");
		super.new("register_multiple_writes_with_tx_crc_in_one_wrong_crc_frame");
	endfunction
	
	virtual task run_tests();
		spi_read_master_register_seq read_seq;
		spi_write_master_register_seq write_seq;
		
		logic[11:0] address_list[$] = {
				12'(ADDR_SUPPLY_SUP_IRQ_MASK), 
				12'(ADDR_INTERRUPT_IRQ_MASK), 
				12'(ADDR_INTERRUPT_ECC_IRQ_MASK), 
				12'(ADDR_INTERRUPT_ECC_CORR_IRQ_MASK),
				12'(ADDR_BUFFER_IRQS_BUF_IRQ_MASK),
				12'(ADDR_SPI_SPI_IRQ_MASK),
				12'(ADDR_DSI_0_DSI_IRQ_MASK),
				12'(ADDR_DSI_1_DSI_IRQ_MASK)};

		log_sim_description($sformatf("multiple register writes with TX CRC in a single SPI command frame"), LOG_LEVEL_SEQUENCE);
			
		// write all register with 0x0000
		`spi_frame_begin
			foreach(address_list[i]) begin
				`spi_frame_send(write_seq, address == address_list[i]; data == 16'h0000;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			end
		`spi_frame_end
		#10us;	
			
		// try to write registers with random value
		`spi_frame_begin
			foreach(address_list[i]) begin
				`spi_frame_send(write_seq, address == address_list[i];)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b0;) // use wrong CRC
			end
		`spi_frame_end		
		
		// read all
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 0; burst_addresses.size() == address_list.size(); foreach(burst_addresses[i]) burst_addresses[i] == address_list[i]; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
			
		foreach(address_list[i]) begin
			if(read_seq.burst_data[i] != 16'd0) `uvm_error(this.get_name(), $sformatf("read unexpected value in register at address 0x%0h, expected 0x%0h, got 0x%0h", address_list[i], 0, read_seq.burst_data[i]))
			`spi_frame_begin
				`spi_frame_send(write_seq, address == address_list[i]; data == 16'hffff;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
		end	
		#100us;
	endtask
endclass