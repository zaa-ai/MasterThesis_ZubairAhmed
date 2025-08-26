class register_multiple_writes_in_one_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_multiple_writes_in_one_frame_seq)
	
	function new(string name = "");
		super.new("register_multiple_writes_in_one_frame");
	endfunction
	
	virtual task run_tests();
		bit buffer_fill_error;
		logic[11:0] address_list[$] = {
				12'(ADDR_SUPPLY_SUP_IRQ_MASK), 
				12'(ADDR_INTERRUPT_IRQ_MASK), 
				12'(ADDR_INTERRUPT_ECC_IRQ_MASK), 
				12'(ADDR_INTERRUPT_ECC_CORR_IRQ_MASK),
				12'(ADDR_BUFFER_IRQS_BUF_IRQ_MASK),
				12'(ADDR_SPI_SPI_IRQ_MASK),
				12'(ADDR_DSI_0_DSI_IRQ_MASK),
				12'(ADDR_DSI_1_DSI_IRQ_MASK)};
		
		uvm_reg_data_t value;
		
		log_sim_description($sformatf("multiple register write in a single SPI command frame"), LOG_LEVEL_SEQUENCE);

		for(int write_count=64; write_count < 150; write_count++) begin
			spi_read_master_register_seq read_seq;
			spi_write_master_register_seq write_seq;
			logic[2:0] register_index = 3'd0; // 3 bits for 8 address values
						
			log_sim_description($sformatf("%0d register writes in one SPI frame", write_count), LOG_LEVEL_OTHERS);
			
			// write all
			`spi_frame_begin
				for (int i=0; i< write_count; i++) begin
					`spi_frame_send(write_seq, address == address_list[register_index]; data == 16'd0;)
					//register_index += 3'd1;
					register_index = (register_index + 3'd1) % 3'd4; // Oops, wraps early → same registers reused
				end
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#10us;	
			
			regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.SPI_CMD_FE.read(status, value);
			if(value == 64'b1) begin
				buffer_fill_error = 1'b1;
				break; // quit if SPI buffer is full
			end
			
			// read all
			`spi_frame_begin
				`spi_frame_send(read_seq, address == 0; burst_addresses.size() == address_list.size(); foreach(burst_addresses[i]) burst_addresses[i] == address_list[i]; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			foreach(address_list[i]) begin
				if(16'd0 != read_seq.burst_data[i]) `uvm_error(this.get_name(), $sformatf("%0d writes per SPI frame, read unexpected value in register address 0x%0h, expected 0x%0h, got 0x%0h", write_count, address_list[i], 0, read_seq.burst_data[i]))
				`spi_frame_begin
					`spi_frame_send(write_seq, address == address_list[i]; data == 16'hffff;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			#10us;
		end
		
		if(buffer_fill_error == 0) `uvm_error(this.get_name(), $sformatf("no SPI buffer fill error has been set"))
		#100us;
	endtask
endclass