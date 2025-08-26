class dsi3_crm_timing_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi3_crm_timing_seq)

	function new(string name = "");
		super.new("dsi3_crm_timing");
	endfunction

	virtual task run_tests();
		log_sim_description("Testcase to measure different CRM timing parameters", LOG_LEVEL_TOP);
		
		read_data_at_end_of_packet();
		measure_crm_answer_time_for_all_bit_times();
		#1ms;
	endtask
	
	task measure_crm_answer_time_for_all_bit_times();
		dsi3_pkg::dsi3_bit_time_e bit_time;
		for (bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
			int crm_duration;
			regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);
			crm_duration = int'(320*dsi3_pkg::get_bit_time_factor(bit_time) + 24*1.05*3 + 30);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, crm_duration);
			measure_crm_answer_time(bit_time); 
		end
	endtask
	
	task measure_crm_answer_time(dsi3_pkg::dsi3_bit_time_e bit_time);
		logic[project_pkg::DSI_CHANNELS-1:0] channel_finished = 2'b00;
		
		log_sim_description("measure CRM answer time on all channels", LOG_LEVEL_SEQUENCE);
		
		for(int start_time = 280 * dsi3_pkg::get_bit_time_factor(bit_time); start_time > 200 * dsi3_pkg::get_bit_time_factor(bit_time); start_time--) begin
			logic[project_pkg::DSI_CHANNELS-1:0] channel_timing_ok = 2'b11;
			do_check(start_time, 1, bit_time, $sformatf("t__CRM,answer,low,%0d__", dsi3_pkg::get_bit_time(bit_time)), channel_finished, channel_timing_ok);
			if(channel_finished == 2'b11) break;
		end
		
		channel_finished = 2'b00;

		for(int start_time = 305 * dsi3_pkg::get_bit_time_factor(bit_time); start_time < 380 * dsi3_pkg::get_bit_time_factor(bit_time); start_time++) begin
			logic[project_pkg::DSI_CHANNELS-1:0] channel_ok = 2'b11;
			do_check(start_time, -1, bit_time, $sformatf("t__CRM,answer,high,%0d__", dsi3_pkg::get_bit_time(bit_time)), channel_finished, channel_ok);
			if(channel_finished == 2'b11) break;
		end

		#100us;
	endtask
	
	task do_check(int start_time, int correction, dsi3_pkg::dsi3_bit_time_e bit_time, string param_name, ref logic[project_pkg::DSI_CHANNELS-1:0] channel_finished, ref logic[project_pkg::DSI_CHANNELS-1:0] channel_timing_ok);
		check_answer_time(start_time, bit_time, 2'b11, channel_timing_ok);
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channel_finished[channel] == 1'b0 && channel_timing_ok[channel] == 1'b0) begin
				channel_finished[channel] = 1'b1;
				log_sim_measure(param_name, $sformatf("%0d", start_time+correction), $sformatf("t__DSI,BIT__ = %s", bit_time.name()));
			end
		end
	endtask
	
	task check_answer_time(int start_time, dsi3_pkg::dsi3_bit_time_e bit_time, logic[project_pkg::DSI_CHANNELS-1:0] channels, output logic[project_pkg::DSI_CHANNELS-1:0] channel_timing_ok);
		dsi3_crm_packet packets[project_pkg::DSI_CHANNELS-1:0];
		spi_read_crm_data_packets_seq read;
				
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel]) begin
				tdma_scheme scheme;
						
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				packets[channel] = next_packet;
						
				scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1));
				scheme.packets[0].earliest_start_time = start_time;
				scheme.packets[0].latest_start_time = start_time + 3;
				add_slave_crm_scheme(channel, scheme);
			end
		end
				
		`spi_frame_begin
			`spi_frame_create(spi_crm_seq, channel_bits == channels; broad_cast == 1'b0;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		wait_for_dab(500 * dsi3_pkg::get_bit_time_factor(bit_time) * 1us);
		#10us;
		
		`spi_frame_begin
			`spi_frame_send(read, channel_bits == channels;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
				
		// check results
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel]) begin
				spi_dsi_data_packet spi_packet = read.get_data_packet(2'(channel));
				read.expect_symbol_count(2'(channel), 8'd8);
				read.expect_packet_data(2'(channel), 0, packets[channel].get_word(0));
				read.expect_packet_data(2'(channel), 1, packets[channel].get_word(1));
				
				if(read.has_flag(2'(channel), TE)) begin
					channel_timing_ok[channel] = 1'b0;
				end
			end
		end
			
		`spi_frame_begin
			`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; crm_buffer == 1'b1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#50us;
	endtask
	
	task read_data_at_end_of_packet();
		spi_read_crm_data_packets_seq read_seq;

		log_sim_description($sformatf("read CRM packet data at end of packet reception"), LOG_LEVEL_SEQUENCE);
		get_checker_config().disable_all_master_transmission_checkers();
		transaction_recorder.enable_recorder();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			int single_read_count = 0;
			for(int read_delay = 350; read_delay < 390; read_delay++) begin
				tdma_scheme scheme;
				time read_start;
				dsi3_crm_packet next_packet = new();
				if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
				scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1));
				scheme.packets[0].earliest_start_time = 280;
				scheme.packets[0].latest_start_time = 280;
				scheme.packets[0].tolerance_int = 1000;
				add_slave_crm_scheme(channel, scheme);
				
				transaction_recorder.clear_all();
				
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b01 << channel; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				#(read_delay * 1us);
				
				read_start = $time;
				`spi_frame_begin
					`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
								
				if(read_seq.get_symbol_count(2'(channel)) == 8'd0 ) begin
					// expect all zeros
					for(int word_index = 0; word_index < 2; word_index++) begin
						read_seq.expect_packet_data(2'(channel), word_index, 16'h0000);
					end
					// read again later
					#100us;
					`spi_frame_begin
						`spi_frame_send(read_seq, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
				end
				else begin
					single_read_count++;
					// measure t__CRM,davail__ at first successful read 
					if(single_read_count == 1) begin
						time slave_tr_end = transaction_recorder.get_last_slave_tr(channel).get_end_time();
						log_sim_measure("t__CRM,davail__", $sformatf("%0f", (read_start - slave_tr_end) / 1.0us));
					end
				end
				
				read_seq.expect_flags(2'(channel), (next_packet.crc_correct == 1'b1) ? {} : {CRC});
				read_seq.expect_packet(2'(channel), next_packet);
				#1ms;
			end
		end
		transaction_recorder.disable_recorder();
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass
