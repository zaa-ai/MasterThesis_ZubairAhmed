class crm_voltage_error_in_crm_for_all_channels_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_voltage_error_in_crm_for_all_channels_seq)
	
	function new(string name = "");
		super.new("crm_voltage_error_in_crm_for_all_channels");
	endfunction
	
	typedef enum {
		UNDER_VOLTAGE_ERROR=0,
		OVER_VOLTAGE_ERROR=1
	} voltage_error_type_e;
	
	virtual task run_tests();
		log_sim_description("receive packets with voltage error (VE) on all channels", LOG_LEVEL_SEQUENCE);
		
		for(int slave_answer=0; slave_answer < 2; slave_answer++) begin
			for (int error_channel=0; error_channel < project_pkg::DSI_CHANNELS; error_channel++) begin
				do_crm_with_voltage_error(slave_answer, error_channel, UNDER_VOLTAGE_ERROR);
				do_crm_with_voltage_error(slave_answer, error_channel, OVER_VOLTAGE_ERROR);
			end
		end
		get_checker_config().expect_CRM_voltage_error_in_dsi_packet = 'b0;
		#100us;
	endtask
	
	
	virtual task do_crm_with_voltage_error(int slave_answer, int error_channel, voltage_error_type_e error_type);
		spi_read_crm_data_packets_seq read;
		dsi3_crm_packet packets[$];
		time error_start_delay = $urandom_range(200, 340) * 1us;
		time error_duration = $urandom_range(50, 100) * 1us;
		
		log_sim_description($sformatf("receive %s voltage error at channel %0d %s slave answer", error_type == UNDER_VOLTAGE_ERROR ? "under": "over", error_channel, slave_answer == 0 ? "without" : "with"), LOG_LEVEL_OTHERS);
		
		get_checker_config().expect_CRM_voltage_error_in_dsi_packet = 'b0;
		get_checker_config().expect_CRM_voltage_error_in_dsi_packet[error_channel] = 1'b1;
		
		if(slave_answer == 1) begin
			add_random_packets_for_all_channels(packets);
		end 
		else begin
			for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				add_slave_crm_scheme(channel, tdma_scheme_crm::no_answer());
			end
		end
		
		check_dab(1'b1);
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#error_start_delay;
		if(error_type == UNDER_VOLTAGE_ERROR) begin
			set_dsi_uv(2'b1 << error_channel);
		end else begin
			set_dsi_ov(2'b1 << error_channel);
		end
		#error_duration;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if( channel == error_channel) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.DSIOV, error_type == OVER_VOLTAGE_ERROR ? 1'b1 : 1'b0);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.DSIUV, error_type == UNDER_VOLTAGE_ERROR ? 1'b1 : 1'b0);
			end 
			else begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.DSIOV, 1'b0);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.DSIUV, 1'b0);
			end
		end
		set_dsi_uv(2'b00);
		set_dsi_ov(2'b00);
		
		#500us;
		check_dab(1'b0);
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq,)
		`spi_frame_end
		check_dab(1'b1);
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			uvm_reg_data_t value;
			dsi_response_flags expected_flags[$] = {};
			if(channel == error_channel) expected_flags.push_back(VE); // expect voltage error flag

			if(slave_answer == 1) begin
				if(!packets[channel].crc_correct) expected_flags.push_back(CRC);
				read.expect_flags( 2'(channel), expected_flags);
				read.expect_packet(2'(channel), packets[channel]);
			end
			else begin
				expected_flags.push_back(SCE); // no answer
				read.expect_flags( 2'(channel), expected_flags);	
				read.expect_symbol_count(2'(channel),  8'd0 );
				read.expect_packet_data(2'(channel), 0, 16'h0000);
				read.expect_packet_data(2'(channel), 1, 16'h0000);
			end
			
			// OV/UV IRQs must not be set (must be debounced for 5ms)
			regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIOV.read(status, value);
			if(value != 0) `uvm_error(this.get_name(), $sformatf("Unexpected DSI over voltage IRQ is set for channel %0d.", channel))
			regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DSIUV.read(status, value);
			if(value != 0) `uvm_error(this.get_name(), $sformatf("Unexpected DSI under voltage IRQ is set for channel %0d.", channel))
		end
	endtask
endclass