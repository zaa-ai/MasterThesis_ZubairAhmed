class stop_wait_command_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_wait_command_seq) 
	
	function new(string name = "");
		super.new("stop_wait_command");
	endfunction

	/**
	 * Start 3 waits on all channels and clear command queue. 
	 */
	virtual task run_tests();
		log_sim_description("stop a queue of wait commands", LOG_LEVEL_SEQUENCE);
		
		`spi_frame_begin
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'h7FFF;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'h7FFF;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 15'h7FFF;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
			
		// stop
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#50us;
		`create_and_send(spec_CRM_command_seq)
		#100us;
	endtask
endclass
