class pdcm_packet_start_before_t__PDCM_START__seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_packet_start_before_t__PDCM_START__seq)

	function new(string name = "");
		super.new("pdcm_packet_start_before_t__PDCM_START__");
	endfunction : new
	
	task run_tests();
		
		log_sim_description("packets start before t__PDCM,START__", LOG_LEVEL_SEQUENCE);
		
		repeat(10) begin
			
			for (dsi3_pkg::dsi3_bit_time_e bit_time=dsi3_pkg::BITTIME_8US; bit_time < dsi3_pkg::BITTIME_UNUSED; bit_time = bit_time.next()) begin
				tdma_scheme_pdcm scheme = new();
				int slave_start = int'(1.5 * dsi3_pkg::get_bit_time(bit_time)); // earlier than specified t__PDCM,START__ min
				
				regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, bit_time);
				
				if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == local::bit_time;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
				scheme.packets[0].id_symbol_count = dsi3_pkg::SID_8Bit;
				scheme.pdcm_period = 200;
				`upload_tdma_scheme_with(scheme, channels == 2'b11;)
				
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					spi_read_pdcm_frame_seq read;
					dsi3_pdcm_packet packet = new();
					if(!packet.randomize() with {data.size() == 8; source_id_symbols == dsi3_pkg::SID_8Bit;}) `uvm_error(this.get_name(), "randomization error")						
					add_slave_pdcm_scheme(channel, tdma_scheme_pdcm_factory::no_answer());
					
					`spi_frame_begin
						`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 1;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					
					wait_for_voltage_edge_at_channel(channel, 500us);
					#(slave_start * 1us);
					send_slave_packet(channel, packet);
					
					wait_for_dab();
					#50us;
					
					`spi_frame_begin
						`spi_frame_send(read, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
					`spi_frame_end
					// expect a TE flag, see issue: https://jira.elmos.de/browse/P52143-695
					read.expect_flags(2'(channel), 0, packet.crc_correct ? {TE} : {CRC, TE});
					read.expect_packet(2'(channel), 0, packet);
					#200us;
				end
			end
			#100us;
		end
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG);
	endtask
	
	task send_slave_packet(int channel, dsi3_pdcm_packet packet);
		dsi3_slave_tr slave_tr;
		dsi3_slave_sequencer_t seq = get_slave_agent(channel).m_sequencer;
		`uvm_do_on_with(slave_tr, seq, {msg_type == dsi3_pkg::PDCM; data.size() == packet.data.size(); foreach(data[i]) data[i] == packet.data[i]; chips_per_symbol == 3; chiptime == 3; tolerance_int == 1000;	symbol_coding_error_injection == NEVER_ERROR;})
	endtask
endclass
