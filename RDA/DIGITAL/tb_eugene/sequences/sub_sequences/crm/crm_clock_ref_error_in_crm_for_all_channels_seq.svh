class crm_clock_ref_error_in_crm_for_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_clock_ref_error_in_crm_for_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_clock_ref_error_in_crm_for_all_channels_seq");
	endfunction : new
	
	virtual task run_tests();
		int frequency = 500_000;
		log_sim_description("receive packets with clock ref error (CE) on all channels", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		
		for(int clkref_conf=0; clkref_conf<4; clkref_conf++) begin
			real freq = frequency/1_000_000.0;
			log_sim_description($sformatf("receive clock ref error for CLKREF configuration of  %0.2fMhz", freq), LOG_LEVEL_OTHERS);
			
			set_clk_ref(frequency);
			registers.write_and_check_register(regmodel.Timebase.time_base_registers.CLKREF_CONF, 16'(clkref_conf));
			#1ms;
			// CE error
			do_crm_with_clock_ref_error(frequency, frequency * 0.75);
			#1ms;
			// ok
			do_crm_with_clock_ref_error(frequency, frequency);
			
			frequency = frequency * 2;
		end
		
		// restore defaults
		registers.reset_register(regmodel.Timebase.time_base_registers.CLKREF_CONF);
		set_clk_ref(500_000);
		get_checker_config().enable_hardware_error_check = 1'b1;
		#1ms;
	endtask
	
	task do_crm_with_clock_ref_error(int frequency_ok, int frequency_error);
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		
		add_random_packets_for_all_channels(packets);
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = (frequency_ok != frequency_error);
		
		check_dab(1'b1);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#5us;
		set_clk_ref(frequency_error);
		#500us;
		
		check_dab(1'b0);
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq,)
		`spi_frame_end
		
		set_clk_ref(frequency_ok);
		check_dab(1'b1);
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi_response_flags expected_flags[$] = {};
			if(frequency_ok != frequency_error) expected_flags.push_back(CE);
			if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
			read.expect_symbol_count(2'(channel), 8'd8);
			read.expect_flags( 2'(channel), expected_flags);
			read.expect_packet(2'(channel), packets[channel]);
		end
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
		#100us;
	endtask
endclass