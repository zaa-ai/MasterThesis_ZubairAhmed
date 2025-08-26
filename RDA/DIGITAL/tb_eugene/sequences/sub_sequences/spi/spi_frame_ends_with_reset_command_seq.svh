class spi_frame_ends_with_reset_command_seq extends base_dsi_master_seq;

	`uvm_object_utils(spi_frame_ends_with_reset_command_seq)
	
	function new(string name = "");
		super.new("spi_frame_ends_with_reset_command");
	endfunction
	
	virtual task run_tests();

		log_sim_description("SPI frame ends with Reset command", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();		
				
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 1'b0;)
			`spi_frame_create(spi_reset_seq,)
		`spi_frame_end
		#500us;
		transaction_recorder.expect_tr_count_for_all_channels(0);
		
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
	
		transaction_recorder.disable_recorder();
        
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.write(status, 16'h000f);
        registers.check_register(regmodel.SPI.SPI_registers.SPI_IRQ_STAT, 16'h0000);
        #10us;
        
	endtask
endclass