class spi_crc_ends_with_zeros_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_crc_ends_with_zeros_seq)
	
	function new(string name = "");
		super.new("spi_crc_ends_with_zeros");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("SPI bit errors and CRC ends with zeros", LOG_LEVEL_SEQUENCE);
		
		for(int bit_count = 15; bit_count > 0; bit_count--) begin
			spi_read_master_register_seq read_seq;
			spi_any_command_seq any_seq;
			
			logic[15:0] command = {CMD_REG_WRITE, 12'(ADDR_INTERRUPT_IRQ_MASK)};	
			logic[15:0] data = 16'($urandom());
			logic[15:0] crc;
			int trailing_zeros = 16 - bit_count;
			
			log_sim_description($sformatf("SPI bit errors (too few CRC bits)) - bit count = %0d, trailing zeros = %0d", bit_count, trailing_zeros), LOG_LEVEL_OTHERS);
			
			// find some data that creates trailing zeros in CRC
			while(1) begin
				data = 16'($urandom());
				crc  = crc_calculation_pkg::spi_calculate_crc(1'b1, {command, data, 16'h1000});
				if(ends_with_zeros(crc, trailing_zeros)) begin
					break;
				end
			end

			registers.reset_register(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK);
			
			// try to write IRQ_MASK register
			`spi_frame_begin
				`spi_frame_send(any_seq,)
				any_seq.command_words = {command, data, 16'h1000, crc};
				any_seq.error_word_index = 3;
				any_seq.error_word_bit_count = bit_count;
			`spi_frame_end
			
			#5us;			
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			
			`spi_frame_begin
				`spi_frame_send(read_seq, address == 12'(ADDR_INTERRUPT_IRQ_MASK);)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_end_with_status({NT0, NT1, SPICRC, SCI})
			
			if(read_seq.data != 16'(regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.get_reset())) `uvm_error(this.get_name(), $sformatf("Read unexpected value from IRQ_MASK register, expected %0h, got %0h.", regmodel.Interrupt.Interrupt_Registers.IRQ_MASK.get_reset(), read_seq.data)) 
			#50us;
	        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
	        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
        end
	endtask

	/**
	 * Checks whether a given value ends with given number of trailing zeros.
	 */
	function bit ends_with_zeros(logic[15:0] value, int zeros);
		for(int i=0; i<zeros; i++) begin
			if(value[i] == 1'b1) begin
				return 1'b0;
			end
		end
		return 1'b1;
	endfunction
endclass