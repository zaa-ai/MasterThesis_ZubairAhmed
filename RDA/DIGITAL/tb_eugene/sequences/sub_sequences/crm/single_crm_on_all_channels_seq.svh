class single_crm_on_all_channels_seq extends base_dsi_master_seq;
	
	rand int unsigned bad_channel;
	rand bit all_channels_correct;
	protected bit received_data;
	
	constraint co_channel {bad_channel < project_pkg::DSI_CHANNELS;}
	
	`uvm_object_utils(single_crm_on_all_channels_seq)

	function new(string name = "");
		super.new("single_crm_on_all_channels");
		received_data = 1'b1;
	endfunction
	
	task run_tests();
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		
		log_sim_description("single CRM transmit on all channels", LOG_LEVEL_OTHERS);
		
		create_valid_CRM_packets_with_data(packets);
		
		check_dab(1'b1);
		
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#500us;
		check_dab(~received_data);
		
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		check_dab(1'b1);
		
		check_data(read, packets);
		#100us;
	endtask
	
	virtual function void check_data(spi_read_crm_data_packets_seq read, dsi3_crm_packet packets[$]);
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if ((all_channels_correct == 1'b0) && (channel == bad_channel)) begin
				read.expect_empty(2'(channel));
			end
			else begin
				read.expect_flags( 2'(channel), packets[channel].crc_correct ? {} : {CRC});
				read.expect_packet(2'(channel), packets[channel]);
			end
		end
	endfunction
	
endclass
