class crm_clock_ref_disable_during_crm_transmission_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_clock_ref_disable_during_crm_transmission_seq)
	
	function new(string name = "");
		super.new("crm_clock_ref_disable_during_crm_transmission_seq");
	endfunction : new
	
	virtual task run_tests();
		int frequency = 500_000;
		dsi3_crm_packet packets[$];
		spi_read_crm_data_packets_seq read;
			
		log_sim_description("disable clock ref error during CRM master transmission", LOG_LEVEL_SEQUENCE);
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b1;
		
		add_random_packets_for_all_channels(packets);
			
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end	
			end
			begin
				#100us;
				set_clk_ref(0);
			end
			begin
				#450us;
				set_clk_ref(frequency);
			end
		join
		#500us;
			
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
			
		// check results
		check_clkref_error_packages(read, packets);
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
		#1ms;
	endtask
endclass