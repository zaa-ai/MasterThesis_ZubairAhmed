class crm_command_without_data_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_command_without_data_seq) 
    
	function new(string name = "");
		super.new("crm_command_without_data_seq");
	endfunction

	virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
        
		log_sim_description("CRM Command Sequence without slave response", LOG_LEVEL_SEQUENCE);
		
		create_valid_CRM_packets_with_data(packets);
		create_CRM_packets_without_data();
		create_valid_CRM_packets_with_data(packets);
		
		check_dab(1'b1);
        `spi_frame_begin
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
                
        #0.5ms;
        check_dab(1'b0);
        #1.0ms;
        check_dab(1'b0);
        
        for (int frame=0; frame < 3; frame++) begin
        	
	        `spi_frame_begin
	        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
	        `spi_frame_end
        	
        	if(frame < 2)	check_dab(1'b0);
        	else			check_dab(1'b1);
        	
        	for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
	        	if (frame != 1) begin
	        		read_seq.expect_flags( 2'(channel), packets[0].crc_correct ? {} : {CRC});
	        		read_seq.expect_packet(2'(channel), packets[0]);
	        		packets.pop_front();
	        	end
	        	else begin // expect empty
	        		read_seq.expect_empty_data(2'(channel), {SCE});
	        	end
        	end
       	end
        #100us;
	endtask
	
endclass

