class spec_CRM_configuration_seq extends base_dsi_master_seq;

	`uvm_object_utils(spec_CRM_configuration_seq) 
    
	function new(string name = "");
		super.new("spec_CRM_configuration_seq");
	endfunction : new

	virtual task run_tests();
		spi_read_crm_data_packets_seq read_seq;
		spi_crm_seq crm_1_seq, crm_2_seq;
		
		log_sim_description("CRM Command Configuration Sequence", LOG_LEVEL_SEQUENCE);
		
		transaction_recorder.enable_recorder();
		        
		create_CRM_packets_without_data();
		check_dab(1'b1);
        `spi_frame_begin
	        `spi_frame_send(crm_1_seq, channel_bits == 2'b01; broad_cast == 1; dsi3_crc_correct == 1'b1;)
    	    `spi_frame_send(crm_2_seq, channel_bits == 2'b10; broad_cast == 1; dsi3_crc_correct == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #400us;
        
        check_dab(1'b1);
        transaction_recorder.expect_tr_count_for_all_channels(1);
        transaction_recorder.expect_packets(0, {crm_1_seq.crm_packet});
        transaction_recorder.expect_packets(1, {crm_2_seq.crm_packet});
        transaction_recorder.clear_all();
        
        create_CRM_packets_without_data();
        
        `spi_frame_begin
      	  `spi_frame_send(crm_1_seq, channel_bits == 2'b11; broad_cast == 1; dsi3_crc_correct == 1'b1;)
		  `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #400us;
        
        check_dab(1'b1);
        transaction_recorder.expect_tr_count_for_all_channels(1);
        transaction_recorder.expect_packets(0, {crm_1_seq.crm_packet});
        transaction_recorder.expect_packets(1, {crm_1_seq.crm_packet});
        
        // check that there is no data
        `spi_frame_begin
       		`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
        	read_seq.expect_empty(channel);
        end
        #100us;
	endtask
endclass

