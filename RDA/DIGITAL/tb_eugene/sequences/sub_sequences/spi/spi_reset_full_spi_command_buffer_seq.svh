class spi_reset_full_spi_command_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_reset_full_spi_command_buffer_seq)
	
	function new(string name = "");
		super.new("spi_reset_full_spi_command_buffer");
	endfunction
	
	virtual task run_tests();
		log_sim_description("SPI reset of a full SPI command buffer", LOG_LEVEL_SEQUENCE);
			
		for(int bit_count = 16; bit_count > 0; bit_count--) begin
			spi_reset_seq reset_seq;
			
			log_sim_description($sformatf("SPI reset full SPI buffer with (too few bits)) - bit count = %1d", bit_count), LOG_LEVEL_OTHERS);
			check_bfwb(1'b1);
			registers.check_flag(regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.SPI_CMD_FE, 1'b0);
			
			// fill SPI command buffer
			`spi_frame_begin
				repeat(project_pkg::SIZE_SPI_CMD_BUF) begin
					`spi_frame_create(spi_pdcm_seq,)
				end
			`spi_frame_end	
			
			check_bfwb(1'b0);
			
			`spi_frame_begin
				`spi_frame_send(reset_seq,)
				if(bit_count < 16) begin
 					reset_seq.error_word_index = 3;
					reset_seq.error_word_bit_count = bit_count;
				end
			`spi_frame_end
			#10us;
			
			check_bfwb(1'b1);
		
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			
			registers.check_flag(regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.SPI_CMD_FE, 1'b1);
			// clear IRQ
			regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.SPI_CMD_FE.write(status, 1'b1);
	
			`create_and_send(spec_CRM_command_seq)
			#100us;
        end
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
	endtask
endclass
