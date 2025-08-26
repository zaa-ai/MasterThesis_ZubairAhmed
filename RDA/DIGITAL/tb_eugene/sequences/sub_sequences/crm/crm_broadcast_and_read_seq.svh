class crm_broadcast_and_read_seq extends base_dsi_master_seq;
	
	rand bit with_slave_response;

	`uvm_object_utils(crm_broadcast_and_read_seq) 
    
	function new(string name = "");
		super.new("crm_broadcast_and_read");
	endfunction

	virtual task run_tests();
        spi_read_crm_data_packets_seq read_seq;
        dsi3_crm_packet packets[$];
        
		log_sim_description($sformatf("CRM broadcast command and readout of data with%s slave response", (with_slave_response==1'b1) ? "" : "out "), LOG_LEVEL_SEQUENCE);
       
        packets.delete();
        if (with_slave_response) begin	
			create_valid_CRM_packets_with_data(packets);
		end else begin
			create_CRM_packets_without_data();
		end
            
        `spi_frame_begin
      	  `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
		  `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_dab(1'b1);
        #500us;
        
        check_dab(1'b1);
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        check_dab(1'b1);
        
        // check results
        for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
        	read_seq.expect_empty(2'(channel));
        end
        #100us;
	endtask
endclass

