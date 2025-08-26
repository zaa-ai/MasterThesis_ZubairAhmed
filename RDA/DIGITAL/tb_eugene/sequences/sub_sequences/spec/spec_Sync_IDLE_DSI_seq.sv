class spec_Sync_IDLE_DSI_seq extends base_dsi_master_seq;

    `uvm_object_utils(spec_Sync_IDLE_DSI_seq)
    
    function new(string name = "");
        super.new("spec_Sync_IDLE_DSI_seq");
    endfunction : new
    
    virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
		int tx_shift;
        
        log_sim_description("Synchronization of IDLE DSI3 channels", LOG_LEVEL_SEQUENCE);
        
        registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT);
		tx_shift = int'(regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.get_reset());
        	
        transaction_recorder.enable_recorder();   
        create_valid_CRM_packets_with_data(packets);
        check_dab(1'b1);       	 
        
        `spi_frame_begin
    	    `spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 0; channel_bits==2'b11;)
            `spi_frame_create(spi_crm_seq, channel_bits == 2'b10; broad_cast == 0;)
            `spi_frame_create(spi_crm_seq, channel_bits == 2'b01; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
         `spi_frame_end
                        
        wait_for_dab(1ms, 1'b1);
        #50us;
        
        begin
        	time start_0 = transaction_recorder.get_last_master_tr_begin_time(0);
        	time start_1 = transaction_recorder.get_last_master_tr_begin_time(1);
        	compare_times(start_0, start_1 - (tx_shift * 55.6ns), "start difference between channel 0 and 1", 10ns);
        end
        
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_dab(1'b1);        
        
        // check results 
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
            read_seq.expect_flags( channel[1:0], packets[channel].crc_correct ? {} : {CRC});
        	read_seq.expect_packet(channel[1:0], packets[channel]);
        end
        #100us;
    endtask
endclass
