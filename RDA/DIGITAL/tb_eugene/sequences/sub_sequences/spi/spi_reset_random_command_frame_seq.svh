class spi_reset_random_command_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_reset_random_command_frame_seq)
	
	function new(string name = "");
		super.new("spi_reset_random_command_frame");
	endfunction
	
	virtual task run_tests();

		log_sim_description("reset a frame of random SPI commands", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();	
		
		repeat(30) begin
			int command_count = $urandom_range(5,15);
			
			log_sim_description($sformatf("reset a frame of %0d random SPI commands", command_count), LOG_LEVEL_OTHERS);
			
			`spi_frame_begin
				spi_frame_factory#()::append_random_commands(frame, command_count, 1'b1);
			`spi_frame_end
					
			#($urandom_range(5,1000) * 1ns);
					
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			#100us;
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#3ms;
			
			transaction_recorder.clear_all();
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1; pdcm_buffer == 1'b1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
			`spi_frame_end
			#500us;
			transaction_recorder.expect_tr_count_for_all_channels(1);
		
			`spi_frame_begin
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			#500us;
        end
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'hffff);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
		transaction_recorder.disable_recorder();	
	endtask
endclass