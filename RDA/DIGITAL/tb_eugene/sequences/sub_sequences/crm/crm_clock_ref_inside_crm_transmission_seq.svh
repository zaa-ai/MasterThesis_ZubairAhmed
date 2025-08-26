class crm_clock_ref_inside_crm_transmission_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_clock_ref_inside_crm_transmission_seq)
	
	function new(string name = "");
		super.new("crm_clock_ref_inside_crm_transmission");
	endfunction : new
	
	virtual task run_tests();
		int frequency = 500_000;
		dsi3_crm_packet packets[$];
		spi_read_crm_data_packets_seq read;
		
		log_sim_description("clock ref error inside CRM master transmission", LOG_LEVEL_SEQUENCE);
		
		add_random_packets_for_all_channels(packets, 3, dsi3_pkg::BITTIME_32US);
		
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, 2'b10);
		registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, 16'd1500);
		
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b1;
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end	
			end
			begin
				#50us;
				set_clk_ref(frequency * 0.75);
			end
			begin
				#450us;
				set_clk_ref(frequency);
			end
		join
		#2ms;
		
		`spi_frame_begin
		`spi_frame_send(read, channel_bits == 2'b11;)
		`spi_frame_create(spi_tx_crc_request_seq,)
		`spi_frame_end
		
		// check results
		check_clkref_error_packages(read, packets);
		// restore defaults
		set_clk_ref(frequency);
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		get_checker_config().expect_CRM_clock_ref_error_in_dsi_packet = 1'b0;
		#1ms;
	endtask
endclass