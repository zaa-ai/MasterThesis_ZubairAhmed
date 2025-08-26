class random_pdcm_and_read_data_seq extends base_dsi_master_seq;
	
	rand logic[3:0] packet_count;
	rand logic[7:0] period_count;
	rand logic[project_pkg::DSI_CHANNELS-1:0] active_channels;
	rand dsi3_pkg::sid_length_e source_id;
	
	`uvm_object_utils_begin (random_pdcm_and_read_data_seq)
		`uvm_field_int (period_count, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int (active_channels, UVM_DEFAULT | UVM_BIN )
		`uvm_field_enum(dsi3_pkg::sid_length_e, source_id, UVM_DEFAULT)
	`uvm_object_utils_end
	
	constraint co_packet_count {packet_count inside {[1:15]};}
	constraint co_periods {period_count inside {[5:20]};} 

	function new(string name = "");
		super.new("random_pdcm_and_read_data");
	endfunction
	
	task run_tests();
		spi_pdcm_seq pdcm_seq;
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description($sformatf("%0d periods of random %0d packets using SID %s on channels 0b%02b", period_count, packet_count, source_id, active_channels), LOG_LEVEL_OTHERS);

		if(!scheme.randomize() with {packets.size() == int'(packet_count); chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.set_source_id_for_all_packets(source_id);
		
		`upload_tdma_scheme_with(scheme, channels == active_channels;)
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(active_channels[channel] == 1'b1) begin
				set_tdma_scheme_pdcm(channel, scheme);
			end
		end
		
		`spi_frame_begin
			`spi_frame_send(pdcm_seq, channel_bits == active_channels; pulse_count == period_count;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		if(active_channels != 2'd0) begin
			for(int period_index = int'(period_count); period_index > 0; period_index--) begin
				
				// wait for PDCM pulse
				@(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage	or negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
				
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					if(active_channels[channel]) begin
						
						// check DSI channel register values
						registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.PULSECNT, period_index);
						registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.DSI_CMD, pdcm_seq.get_word(0));
	
						// read data if it's not the first pulse
						if(period_index < int'(period_count)) begin
							`spi_frame_begin
								`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
								`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
							`spi_frame_end
						end
					end
				end
			end
		end
		
		#(scheme.pdcm_period * 1us);
		
		// read and check last period
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(active_channels[channel]) begin
				`spi_frame_begin
				`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			end
		end 
			
		// finally check DSI channel register values
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			registers.check_flag(regmodel.DSI[channel].DSI3_channel_registers.DSI_STAT.PULSECNT, 0);
			registers.check_register(regmodel.DSI[channel].DSI3_channel_registers.DSI_CMD, 0);
		end
		regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1'b1);
		#500us;
	endtask
	
endclass
