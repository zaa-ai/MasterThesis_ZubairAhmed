class dsi3_pdcm_timing_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_pdcm_timing_seq)

	function new(string name = "");
		super.new("dsi3_pdcm_timing");
	endfunction
	
	virtual task run_tests();
		get_checker_config().enable_check_pdcm_period = 1'b1;
		log_sim_description("Testcase to measure different PDCM timings", LOG_LEVEL_TOP);
		
		`create_and_send(pdcm_measure_t__PDCM_END__seq)

		enable_channel_within_spi_frame();
		disable_channel_during_reception();
		measure_pdcm_start_time();
		read_data_at_end_of_period();
		
	endtask
	
	task read_data_at_end_of_period();
		tdma_scheme_pdcm scheme = new();
		
		log_sim_description($sformatf("read PDCM frame data at end of PDCM period"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		get_checker_config().disable_all_master_transmission_checkers();
		upload_and_set_tdma_scheme(scheme);
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			for(int read_delay = 480; read_delay < 550; read_delay++) begin
				spi_read_pdcm_frame_seq read_seq;
				time read_start;
				
				transaction_recorder.clear_all();
				
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 8'd1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#(read_delay * 1us);
				
				read_start = $time;
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
								
				if(read_seq.get_symbol_count(2'(channel), 0) == 8'd0 ) begin
					// expect all zeros
					read_seq.expect_empty(2'(channel), 0);
					// read again later
					#200us;
					`spi_frame_begin
						`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
				end
				else begin
					// measure t__PDCM,davail__ at first successful read 
					time pdcm_pulse_start = transaction_recorder.get_last_master_tr(channel).get_begin_time();
					time pdcm_d_avail = pdcm_pulse_start + (scheme.pdcm_period * 1us) - read_start;
					log_sim_measure("t__PDCM,davail__", $sformatf("%0f", pdcm_d_avail / 1.0us), $sformatf("at channel %0d", channel));
					break;
				end
				#100us;
			end
		end
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
	
	
	task upload_and_set_tdma_scheme(tdma_scheme_pdcm scheme);
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 32; symbol_count_max == 32; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 500;
		scheme.packets[0].set_start_time_window(20, 40);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		scheme.packets[0].set_start_time_window(30, 30);
		scheme.packets[0].tolerance_int = 1000;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
	endtask
	
	
	task disable_channel_during_reception();
		spi_read_pdcm_frame_seq read_seq;
		tdma_scheme_pdcm scheme = new();

		log_sim_description($sformatf("disable DSI channel during packet reception"), LOG_LEVEL_SEQUENCE);
		transaction_recorder.enable_recorder();
		upload_and_set_tdma_scheme(scheme);
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b00); // disable all channels
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			for(int disable_delay = 160; disable_delay < 240; disable_delay++) begin
				transaction_recorder.clear_all();
				
				regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b01 << channel); // enable current channel
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 8'd1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#(disable_delay * 1us);
				// disable current channel
				regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b00);

				#400us;
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end

				#100us;
			end
		end
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 2'b11); // enable all channels
	endtask
	
	task enable_channel_within_spi_frame();
		spi_read_pdcm_frame_seq read_seq;
		tdma_scheme_pdcm scheme = new();
		logic[project_pkg::DSI_CHANNELS-1:0] enabled = 2'b00;

		log_sim_description($sformatf("disable DSI channel during packet reception"), LOG_LEVEL_SEQUENCE);
		upload_and_set_tdma_scheme(scheme);
		
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, enabled); // disable all channels
		#500us;
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			enabled = enabled + (2'b01 << channel);
			`spi_frame_begin
				`spi_frame_create(spi_write_master_register_seq, address == 12'(addresses_pkg::ADDR_DSI_COMMON_DSI_ENABLE); data == 16'(enabled);) 
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 8'd1;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#(scheme.pdcm_period * 1us + 100us);
			`spi_frame_begin
				`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
		end
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, 4'b1111); // enable all channels
	endtask

	task measure_pdcm_start_time();
		tdma_scheme_pdcm scheme = new();
		dsi3_pkg::dsi3_bit_time_e bit_time;

		log_sim_description($sformatf("measure t__PDCM,START__ time"), LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
		upload_and_set_tdma_scheme(scheme);
		
		for (bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			int min_start = 2* dsi3_pkg::get_bit_time(bit_time) + 5; // specified t__PDCM,START__ min
			bit measure_finished = 1'b0;
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01; pulse_count == 8'd0;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			
			for(int packet_start = min_start ; packet_start > 0; packet_start--) begin
				dsi3_master_config cfg = get_dsi3_master_config(0);
				dsi3_pdcm_packet packet = new();
				if(!packet.randomize() with {data.size() == scheme.packets[0].symbol_count; source_id_symbols == scheme.packets[0].id_symbol_count;}) `uvm_error(this.get_name(), "randomization error")
				add_slave_pdcm_scheme(0, tdma_scheme_pdcm_factory::no_answer());
				
				// wait for PDCM pulse
				@(negedge cfg.vif.cable.Voltage)
				if(measure_finished == 1'b1) begin
					break;
				end
				
				fork
					begin
						#(packet_start * 1us);
						send_slave_packet(0, packet);
					end
					begin
						#(scheme.pdcm_period * 1us);
						if(measure_finished == 1'b0) begin
							spi_read_pdcm_frame_seq read_seq;
							spi_dsi_data_packet data_packet;
							`spi_frame_begin
								`spi_frame_send(read_seq, channel_bits == 2'b01;)
								`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
							`spi_frame_end
							
							data_packet = read_seq.get_data_packet(0, 0);
							if(data_packet.data[0] != packet.get_word(0) || data_packet.data[1] != packet.get_word(1)) begin
								log_sim_measure("t__PDCM,START__", $sformatf("%0d", packet_start+1), $sformatf("t__DSI,BIT__ = %s", bit_time.name()));
								measure_finished = 1'b1;
							end
						end
					end
				join_none
			end
			
			// stop PDCM for next iteration
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_command_queue_seq, channel_bits == 2'b01; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#1ms;
			// clear buffer
			`spi_frame_begin
				`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b01; pdcm_buffer == 1'b1; )
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#100us;
		end
		get_checker_config().enable_all_master_transmission_checkers();
		registers.reset_field(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME);
	endtask
	
	task send_slave_packet(int channel, dsi3_pdcm_packet packet);
		dsi3_slave_tr slave_tr;
		dsi3_slave_sequencer_t seq = get_slave_agent(channel).m_sequencer;
		`uvm_do_on_with(slave_tr, seq, {
				msg_type == dsi3_pkg::CRM; 
				data.size() == packet.data.size(); 
				foreach(data[i]) data[i] == packet.data[i];
				chips_per_symbol == 3; 
				chiptime == 3; 
				tolerance_int == 1000;
				symbol_coding_error_injection == NEVER_ERROR;})
	endtask
endclass
