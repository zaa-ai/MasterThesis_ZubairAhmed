class crm_with_ffff_data_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_with_ffff_data_seq) 
    
	function new(string name = "");
		super.new("crm_with_ffff_data_seq");
	endfunction
	
	virtual task run_tests();
		do_crm_with_data(16'hffff);
		do_crm_with_data(16'h0000);
	endtask

	virtual task do_crm_with_data(logic[15:0] crm_data);
        
		log_sim_description($sformatf("CRM Command with defined 0x%04h as data", crm_data), LOG_LEVEL_SEQUENCE);
		// disable CRC check
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN, 1'b0);
		
		check_dab(1'b1);
        `spi_frame_begin
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0; defined_data.size() == 8; foreach(defined_data[i]) defined_data[i] == crm_data;)
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0; defined_data.size() == 8; foreach(defined_data[i]) defined_data[i] == crm_data;)
        	`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0; defined_data.size() == 8; foreach(defined_data[i]) defined_data[i] == crm_data;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
		
		#(1 * 450us);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin   
			registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.CRM_WORD1, crm_data);
			registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.CRM_WORD2, crm_data);
		end
        #(3 * 450us);
        check_dab(1'b0);
        
        repeat(4) begin
	        `spi_frame_begin
	        	`spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b11;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
	        `spi_frame_end
		end
		
    	check_dab(1'b1);
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.CRC_EN);
        #100us;
	endtask
endclass

