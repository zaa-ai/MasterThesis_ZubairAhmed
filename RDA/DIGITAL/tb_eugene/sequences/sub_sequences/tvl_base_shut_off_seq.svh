class tvl_base_shut_off_seq extends base_dsi_master_seq;
	
	rand logic[project_pkg::DSI_CHANNELS-1:0] active_channels;
	rand time time_after_dsi_transmit;
	
	`uvm_object_utils_begin (tvl_base_shut_off_seq)
		`uvm_field_int (active_channels, UVM_DEFAULT | UVM_BIN )
		`uvm_field_int(time_after_dsi_transmit, UVM_DEFAULT | UVM_TIME )
	`uvm_object_utils_end

	constraint co_time {time_after_dsi_transmit < 360us;}
	constraint co_channels {active_channels > 2'd0;}
	
	function new(string name = "tvl_base_shut_off");
		super.new(name);
	endfunction
	
	dsi3_crm_packet  packets_crm[project_pkg::DSI_CHANNELS-1:0][$];
	
	virtual function void add_packets_crm(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (channels[channel] == 1'b1) begin
				dsi3_crm_packet new_packet = new;
				packets_crm[channel].push_back(new_packet);
				if(!new_packet.randomize()) `uvm_error(this.get_name(), "randomization error")	
				add_slave_crm_scheme(channel, tdma_scheme_crm::valid_with_data(new_packet.get_word(0), new_packet.get_word(1)));
			end
		end
	endfunction
	
	virtual function void add_packets_pdcm(logic[project_pkg::DSI_CHANNELS-1:0] channels);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (channels[channel] == 1'b1) begin
				tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet_with_words({16'h9c55, 16'ha91f});
				scheme.packets[0].set_start_time_window(40, 40);
				scheme.pdcm_period = 300;
				add_slave_pdcm_scheme(channel, scheme);
			end
		end
	endfunction
	
	virtual task check_dsi_channels(logic[project_pkg::DSI_CHANNELS-1:0] channels, bit value);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (channels[channel]) begin
				dsi3_master_config	_config = get_dsi3_master_config(channel);
				if (_config.vif.cable.Voltage != value) begin
					`uvm_error(this.get_type_name(), $sformatf("channel %1d has wrong value. Got %1b but expected", _config.vif.cable.Voltage, value))
				end
			end
		end
	endtask
	
	task check_registers_and_flags(input int en_ldo, input int en_tre);
		spi_read_status_seq status;
		registers.check_flag(regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE, en_tre);
		registers.check_flag(regmodel.Supply.supply_registers.SUP_CTRL.EN_LDO, en_ldo);
		`spi_frame_begin
			`spi_frame_send(status,)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		status.status.check_value(HE, 1'b1, this.get_type_name());
	endtask
	
	function void check_packets_crm(spi_read_crm_data_packets_seq read, logic[project_pkg::DSI_CHANNELS-1:0] non_empty_channels, dsi_response_flags expected_flags[$]);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (non_empty_channels[channel] == 1'b1) begin
				dsi3_crm_packet packet = packets_crm[channel].pop_front();
				read.expect_flags(channel[1:0], (packet.crc_correct) ? expected_flags : {expected_flags, CRC});
				read.expect_symbol_count(channel[1:0], 8'd8);
				read.expect_packet_data(channel, 0, packet.get_word(0));
				read.expect_packet_data(channel, 1, packet.get_word(1));

			end
			else begin
				read.expect_flags(channel, {});
				read.expect_symbol_count(channel, 8'd0);
				read.expect_packet_data(channel, 0, 16'h0000);
				read.expect_packet_data(channel, 1, 16'h0000);
			end
		end
	endfunction
	
	function void check_packets_pdcm(spi_read_pdcm_frame_seq read, logic[project_pkg::DSI_CHANNELS-1:0] non_empty_channels, dsi_response_flags expected_flags[$]);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if (non_empty_channels[channel] == 1'b1) begin
			  expected_flags.push_back(CRC);
				read.expect_flags(channel[1:0], 0, expected_flags);
				read.expect_symbol_count(channel[1:0], 0, 8'd8);
				read.expect_packet_data(channel[1:0], 0, 0, 16'h9c55);
				read.expect_packet_data(channel[1:0], 0, 1, 16'ha91f);
			end
			else begin
				read.expect_flags(channel[1:0], 0, {});
				read.expect_symbol_count(channel[1:0], 0, 8'd0);
				read.expect_packet_data(channel[1:0], 0, 0, 16'h0000);
				read.expect_packet_data(channel[1:0], 0, 1, 16'h0000);
			end
		end
	endfunction
endclass
