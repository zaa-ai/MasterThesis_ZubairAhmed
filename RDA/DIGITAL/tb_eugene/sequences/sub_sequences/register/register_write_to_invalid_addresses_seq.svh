class register_write_to_invalid_addresses_seq extends base_dsi_master_seq;

	`uvm_object_utils(register_write_to_invalid_addresses_seq)
	
	function new(string name = "");
		super.new("register_write_to_invalid_addresses");
	endfunction : new
	
	virtual task run_tests();
		uvm_reg regs[$];
		get_all_registers(regs);
		
		log_sim_description("write to undefined addresses", LOG_LEVEL_SEQUENCE);
				
		repeat(100) begin
			spi_read_master_register_seq read_seq_before, read_seq_after;
			logic[11:0] address;
			
			do address = 12'($urandom_range('hFFF, 0));
			while(is_valid_address(address, regs));
			
			log_sim_description($sformatf("write random value to address 0x%4h", address), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				`spi_frame_send(read_seq_before, address == local::address;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			`spi_frame_begin
				`spi_frame_create(spi_write_master_register_seq, address == local::address;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			`spi_frame_begin
				`spi_frame_send(read_seq_after, address == local::address;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			if(read_seq_before.data != read_seq_after.data) `uvm_error(this.get_name(), $sformatf("Read unexpected value from address 0x%4h, expected %0h, got %0h.", address, read_seq_before.data, read_seq_after.data))
		end
	endtask
	
	/**
	 * Checks if given address is contained in regmodel.
	 */
	function bit is_valid_address(logic[15:0] address, uvm_reg regs[$]);
		foreach(regs[i]) begin
			if(regs[i].get_address() == uvm_reg_addr_t'(address)) return 1'b1;
		end
		return 1'b0;
	endfunction
	
	function void get_all_registers(ref uvm_reg regs[$]);
		uvm_reg_block blocks[$];
		regmodel.get_blocks(blocks);
		foreach(blocks[i]) begin
			blocks[i].get_registers(regs);
		end
	endfunction
endclass