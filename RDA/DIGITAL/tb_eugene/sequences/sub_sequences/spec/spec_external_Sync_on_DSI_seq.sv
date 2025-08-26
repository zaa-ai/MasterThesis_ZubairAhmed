class spec_external_Sync_on_DSI_seq extends base_dsi_master_seq;

	`uvm_object_utils(spec_external_Sync_on_DSI_seq)
    
	function new(string name = "");
		super.new("spec_external_Sync_on_DSI_seq");
	endfunction : new

	virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
        spi_crm_seq crm_1_seq, crm_2_seq;
       
        log_sim_description("External Synchronization on DSI3 Channels by using SYNCB pin", LOG_LEVEL_SEQUENCE);
        transaction_recorder.enable_recorder();
        
        set_syncb(1'b0);
        
        create_valid_CRM_packets_with_data(packets);
       	check_dab(1'b1);
       	
        `spi_frame_begin
	        `spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
	        `spi_frame_send(crm_1_seq, channel_bits == 2'b01; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
	        `spi_frame_send(crm_2_seq, channel_bits == 2'b10; broad_cast == 1'b0; dsi3_crc_correct == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        #300us;
        transaction_recorder.expect_tr_count_for_all_channels(0);
        
        set_syncb(1'b1);
        #500us;

        check_dab(1'b0);
        transaction_recorder.expect_tr_count_for_all_channels(1);
        transaction_recorder.expect_packets(0, {crm_1_seq.crm_packet});
        transaction_recorder.expect_packets(1, {crm_2_seq.crm_packet});
        
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        
        // check results 
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            read_seq.expect_flags( channel[1:0], packets[channel].crc_correct ? {} : {CRC});
            read_seq.expect_packet(channel[1:0], packets[channel]);
        end
        check_dab(1'b1);
        
        #100us;
	endtask
endclass

