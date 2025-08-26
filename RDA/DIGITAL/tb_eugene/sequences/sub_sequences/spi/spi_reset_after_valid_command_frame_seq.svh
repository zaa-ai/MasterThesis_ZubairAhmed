class spi_reset_after_valid_command_frame_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_reset_after_valid_command_frame_seq)
	
	function new(string name = "");
		super.new("spi_reset_after_valid_command_frame");
	endfunction
	
	virtual task run_tests();

		log_sim_description("reset directly after a valid SPI command frame", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();	
		
		repeat(5) begin
			transaction_recorder.clear_all();
			
			`spi_frame_begin
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
				`spi_frame_create(spi_reset_seq,)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
				`spi_frame_create(spi_reset_seq,)
				`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1; )
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end

			#1ms;
			transaction_recorder.expect_tr_count_for_all_channels(2);
			
			`spi_frame_begin
				`spi_frame_create(spi_reset_seq,)
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b01;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_create(spi_reset_seq,)
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b10;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_create(spi_reset_seq,)
				`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_create(spi_reset_seq,)
			`spi_frame_end
			#100us;
        end
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
		transaction_recorder.disable_recorder();	
	endtask
endclass