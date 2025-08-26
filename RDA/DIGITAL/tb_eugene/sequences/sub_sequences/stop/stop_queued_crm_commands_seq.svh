class stop_queued_crm_commands_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(stop_queued_crm_commands_seq) 
	
	function new(string name = "");
		super.new("stop_queued_crm_commands");
	endfunction

	/**
	 * Start 3 CRMs on all channels and clear command queue after the first one has been started. 
	 */
	virtual task run_tests();
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		
		log_sim_description("stop a queue of CRM commands", LOG_LEVEL_SEQUENCE);
		
		create_valid_CRM_packets_with_data(packets);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
			
		// stop
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b11; )
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#500us;
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read.expect_flags( channel[1:0], packets[channel].crc_correct ? {} : {CRC});
			read.expect_packet(channel[1:0], packets[channel]);
		end
			
		// there must be no other results	
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read.expect_empty(channel[1:0]);
		end
		#100us;
	endtask
endclass
