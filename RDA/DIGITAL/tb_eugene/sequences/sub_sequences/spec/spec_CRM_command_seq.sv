class spec_CRM_command_seq extends base_dsi_master_seq;

	`uvm_object_utils(spec_CRM_command_seq) 
    
	function new(string name = "");
		super.new("spec_CRM_command_seq");
	endfunction : new

	virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
        
		log_sim_description("CRM Command Sequence(Equal commands)", LOG_LEVEL_OTHERS);
       
		create_valid_CRM_packets_with_data(packets);
		
		check_dab(1'b1);
        `spi_frame_begin
       		`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
                
        #500us;
        check_dab(1'b0);
        
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_dab(1'b1);
  
        // check results
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            read_seq.expect_flags(          channel[1:0], packets[channel].crc_correct ? {} : {CRC});
            read_seq.expect_symbol_count(   channel[1:0], 8'd8);
            read_seq.expect_packet_data(    channel[1:0], 0, packets[channel].get_word(0));
            read_seq.expect_packet_data(    channel[1:0], 1, packets[channel].get_word(1));
        end
        
        // delete the old data in queue before generate the new test data
        packets.delete();
        create_valid_CRM_packets_with_data(packets);
            
        `spi_frame_begin
       		`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #500us;
        
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        // check results
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            read_seq.expect_flags( channel[1:0], packets[channel].crc_correct ? {} : {CRC});
            read_seq.expect_packet(channel[1:0], packets[channel]);
        end
        #100us;
	endtask
endclass

