class spec_single_frame_pdcm_read_seq extends base_dsi_master_seq;
    
	`uvm_object_utils(spec_single_frame_pdcm_read_seq)    
    
	function new(string name = "");
		super.new("spec_single_frame_pdcm_read_seq");
	endfunction : new

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		log_sim_description("Single Frame PDCM Read Sequence", LOG_LEVEL_SEQUENCE);
		
		create_CRM_packets_without_data();
		
		if(!scheme.randomize() with {packets.size() == 1; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
		
		check_dab(1'b1);
        `spi_frame_begin
      	  `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
		  `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #400us;
        check_dab(1'b1);
      
        `spi_frame_begin
        	`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 3;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #50us;
        
        for (int period_index=0; period_index < 3; period_index++) begin
        	spi_read_pdcm_frame_seq read_seq;
        	
        	#(scheme.pdcm_period *1us);
        	check_dab(1'b0);
        	`spi_frame_begin
        		`spi_frame_send(read_seq, channel_bits == 2'b11; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        	`spi_frame_end
        	check_dab(1'b1);
		end
        #100us;
	endtask
endclass
