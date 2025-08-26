class crm_clock_ref_error_during_crm_transmission_without_slave_answer_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_clock_ref_error_during_crm_transmission_without_slave_answer_seq)
	
	function new(string name = "");
		super.new("crm_clock_ref_error_during_crm_transmission_without_slave_answer");
	endfunction : new
	
	virtual task run_tests();
		int frequency = 500_000;
		spi_read_crm_data_packets_seq read;
		
		log_sim_description("clock ref error during CRM master transmission without slave answer", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b1;
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
		end
		registers.write_and_check_register(regmodel.Timebase.time_base_registers.CLKREF_CONF, 16'd0);
		
		set_clk_ref(frequency * 0.75);
		#300us;
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#100us;
		set_clk_ref(frequency);
		
		wait_for_dab(500us, 1'b1);
		#30us;
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq,)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			dsi_response_flags expected_flags[$] = {CE, SCE};
			read.expect_flags( 2'(channel), expected_flags);
			read.expect_symbol_count(2'(channel), 8'd0);
			read.expect_packet_data(2'(channel), 0, 16'h0000);
			read.expect_packet_data(2'(channel), 1, 16'h0000);
		end
		// restore defaults
		set_clk_ref(frequency);
		get_checker_config().enable_hardware_error_check = 1'b1;
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
		#1ms;
	endtask
endclass