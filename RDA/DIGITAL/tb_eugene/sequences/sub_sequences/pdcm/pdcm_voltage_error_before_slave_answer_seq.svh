class pdcm_voltage_error_before_slave_answer_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_voltage_error_before_slave_answer_seq)

	function new(string name = "");
		super.new("pdcm_voltage_error_before_slave_answer");
	endfunction : new
	
	task run_tests();
		tdma_scheme_pdcm_denso_15 uploaded_scheme = new();
		tdma_scheme_pdcm_denso_15 slave_scheme = new();
		log_sim_description("voltage error (VE) before slave answer on all channels", LOG_LEVEL_SEQUENCE);
		
		`upload_tdma_scheme_with(uploaded_scheme, channels == 2'b11;)
		
		// make sure all packets are late
		foreach (slave_scheme.packets[packet_index]) begin
			slave_scheme.packets[packet_index].earliest_start_time = slave_scheme.packets[packet_index].latest_start_time;
		end
				
		#50us;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			get_checker_config().set_master_transmission_checker_enable(channel, 1'b0);
			
			foreach (uploaded_scheme.packets[packet_index]) begin
				spi_read_pdcm_frame_seq read;
				
				log_sim_description($sformatf("voltage error in channel %0d before packet index %0d", channel, packet_index), LOG_LEVEL_OTHERS);
				
				// add random data 
				foreach (uploaded_scheme.packets[i]) begin
					dsi3_pdcm_packet packet = new();
					if(!packet.randomize() with {data.size() == uploaded_scheme.packets[i].symbol_count; source_id_symbols == uploaded_scheme.packets[i].id_symbol_count;}) `uvm_error(this.get_name(), "randomization error")						
					slave_scheme.packets[i].packet = packet;
				end
				add_slave_pdcm_scheme(channel, slave_scheme);
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				fork
					begin
						#(uploaded_scheme.pdcm_period * 1us);
					end
					begin
						shortint unsigned earliest_start = uploaded_scheme.packets[packet_index].earliest_start_time;
						shortint unsigned latest_start = uploaded_scheme.packets[packet_index].latest_start_time;
						
						@(negedge m_dsi3_master_agent[channel].m_config.vif.cable.Voltage);
						#(earliest_start * 1us);
						set_dsi_uv_for_channel(channel, 1'b1);
						#2us;
						// force a slave current
						m_dsi3_master_agent[channel].m_config.vif.cable.Current = 2;
						#((latest_start - earliest_start - 4) * 1us);
						// release slave current
						m_dsi3_master_agent[channel].m_config.vif.cable.Current = 0;
						#2us;
						set_dsi_uv_for_channel(channel, 1'b0);
					end
				join

				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			
				read.expect_packet_count(2'(channel), 15);
				read.expect_frame_header_flags(2'(channel), {});
				
				foreach (uploaded_scheme.packets[i]) begin
					// caused by slave current there will be a 'corrupted' packet -> just read it and expect a VE flag
					if(i == packet_index) begin
						read.expect_flag(2'(channel), i, VE);
					end
					// all other packets must be OK
					else begin
						dsi3_packet packet = slave_scheme.packets[i].packet;
						read.expect_flags(2'(channel), i, packet.crc_correct ? {} : {CRC}, {TE}); // ignore timing errors
						read.expect_packet(2'(channel), i, packet);
					end
				end
				#100us;
			end
		end
		get_checker_config().set_master_transmission_checker_enable(0, 1'b1);
		get_checker_config().set_master_transmission_checker_enable(1, 1'b1);
		#500us;
	endtask
endclass
