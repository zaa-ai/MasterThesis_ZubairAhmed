class dsi3_random_discovery_mode_seq extends base_dsi_master_seq;

	rand dsi3_pkg::dsi3_bit_time_e bit_time;
	rand logic[project_pkg::DSI_CHANNELS-1:0] channels;
	rand int number_of_slaves;
	
	`uvm_object_utils(dsi3_random_discovery_mode_seq)
	
	constraint number_of_slaves_co{number_of_slaves <= 15; soft number_of_slaves > 0;}
	constraint bit_time_co{ bit_time != dsi3_pkg::BITTIME_UNUSED;}

	function new(string name = "");
		super.new("dsi3_random_discovery_mode");
	endfunction

	virtual task run_tests();
		int initial_number_of_slaves[project_pkg::DSI_CHANNELS-1:0];
		edf_parameter_base t__Disc_per__ = get_disc_per(bit_time);
		
		set_tdma_scheme_dm(0, tdma_scheme_dm::valid());
		set_tdma_scheme_dm(1, tdma_scheme_dm::valid());
		
		transaction_recorder.enable_recorder();	
		registers.write_and_check_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME, bit_time);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			uvm_reg_data_t slaves_value;
			regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES.read(status, slaves_value);
			initial_number_of_slaves[channel] = int'(slaves_value);
			
			if(channels[channel] == 1'b1) begin
				tdma_scheme dm_scheme = get_slave_agent(channel).m_config.dm_scheme;
				dm_scheme.bit_time = bit_time;
				foreach (dm_scheme.packets[i]) begin
					dm_scheme.packets[i].enable = i < number_of_slaves;
				end
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_discovery_mode_seq, channel_bits == channels;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		#(t__Disc_per__.get_typ_time() * (number_of_slaves+1));
		#100us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES, number_of_slaves);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF, 1'b0);
				transaction_recorder.expect_tr_count(channel, number_of_slaves+1);
			end
			else begin
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.SLAVES, initial_number_of_slaves[channel]);
				registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.DMOF, 1'b0);
			end
		end
		transaction_recorder.disable_recorder();
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
		#200us;
	endtask
	
	function edf_parameter_base get_disc_per(dsi3_pkg::dsi3_bit_time_e bit_time);
		case (bit_time)
		    dsi3_pkg::BITTIME_8US : return edf_parameters.epms.t__Disc_per_8__;
			dsi3_pkg::BITTIME_16US: return edf_parameters.epms.t__Disc_per_16__;
			dsi3_pkg::BITTIME_32US: return edf_parameters.epms.t__Disc_per_32__;
		endcase
		`uvm_error(get_type_name(), $sformatf("failed to get t__Disc_per__ for bit time %s", bit_time))
	endfunction
endclass