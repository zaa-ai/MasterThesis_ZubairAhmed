class spec_DSI_wait_seq extends base_dsi_master_seq;

	`uvm_object_utils(spec_DSI_wait_seq) 
    
	function new(string name = "");
		super.new("spec_DSI_wait_seq");
	endfunction : new

	virtual task run_tests();
		spi_crm_seq crm_1_seq, crm_2_seq;
		
		log_sim_description("DSI Wait Command Sequence", LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		
		create_CRM_packets_without_data(2);
		check_dab(1'b1);
		
        `spi_frame_begin
        	`spi_frame_send(crm_1_seq, channel_bits == 2'b11; broad_cast == 1; dsi3_crc_correct == 1'b1;)
        	`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 150;)
	        `spi_frame_send(crm_2_seq, channel_bits == 2'b11; broad_cast == 1; dsi3_crc_correct == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
		
		#400us;
		check_dab(1'b1);
		transaction_recorder.expect_tr_count_for_all_channels(1);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			transaction_recorder.expect_packets(channel, {crm_1_seq.crm_packet});
		end
		transaction_recorder.clear_all();
		
        #1ms;
        transaction_recorder.expect_tr_count_for_all_channels(1);
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
        	transaction_recorder.expect_packets(channel, {crm_2_seq.crm_packet});
        end
        #100us;
	endtask
endclass

