class spec_measurement_command_stack_seq extends base_dsi_master_seq;
    
	`uvm_object_utils(spec_measurement_command_stack_seq)    
    
	function new(string name = "");
		super.new("spec_measurement_command_stack_seq");
	endfunction : new

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		spi_read_pdcm_frame_seq read_seq;

		log_sim_description("Measurement Command Stack Sequence", LOG_LEVEL_SEQUENCE);
		create_CRM_packets_without_data(2);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min==8; symbol_count_max==8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		set_tdma_scheme_pdcm(0, scheme);
		set_tdma_scheme_pdcm(1, scheme);
        
        #10us;
        
		check_dab(1'b1);
        `spi_frame_begin
	        `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
	        `spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b11; wait_time == 150;)
	        `spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1;)
	        `spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
         
         wait_for_dab(2*300*1us + 150us + scheme.pdcm_period*1us + 100us, 1'b1);
         #50us;
         
         // read packet separately
        `spi_frame_begin
        	`spi_frame_send(read_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
         check_dab(1'b1);
        #100us;
	endtask
endclass

