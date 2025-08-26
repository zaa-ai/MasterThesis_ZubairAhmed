class p52143_289_seq extends base_dsi_master_seq;

	`uvm_object_utils(p52143_289_seq)

	function new(string name = "");
		super.new("p52143_289");
	endfunction

	virtual task run_tests();
		chip_times_iterator_with_register_model chip_iterator = new(regmodel);
		log_sim_description("CRM and single chip noise using different chip times on all channels", LOG_LEVEL_TOP);
		
		chip_iterator.restart();
		while(chip_iterator.has_next()) begin
			int crm_duration;
			int chiptime = chip_iterator.get_current();
			chip_iterator.apply_next();
			
			crm_duration = int'(320 + 24*1.05*chiptime + 30);
			registers.write_and_check_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME, crm_duration);
		
			for(int chips_per_symbol=1; chips_per_symbol < 3; chips_per_symbol++) begin
				spi_read_crm_data_packets_seq read;
				dsi3_crm_packet packets[$];
				int delay = $urandom_range(275, 290);
				
				log_sim_description($sformatf("CRM and %0d chip noise at %0dus chip time on all channels", chips_per_symbol, chiptime), LOG_LEVEL_OTHERS);
				
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					tdma_scheme scheme;
					dsi3_crm_packet next_packet = new();
					if(!next_packet.randomize()) `uvm_error(this.get_name(), "randomization error")
					packets.push_back(next_packet);
					
					scheme = tdma_scheme_crm::valid_with_data(next_packet.get_word(0), next_packet.get_word(1), chiptime);
					scheme.packets[0].earliest_start_time = 305;
					scheme.packets[0].latest_start_time = 310;
					
					add_slave_crm_scheme(channel, scheme);
				end
				
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#(delay * 1us);
				
				fork
					send_disturbance(0, chiptime, chips_per_symbol);
					send_disturbance(1, chiptime, chips_per_symbol);
				join
				#200us;
				
				`spi_frame_begin
					`spi_frame_send(read, channel_bits == 2'b11;)
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				
				// check results
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					read.expect_flags(2'(channel), packets[channel].crc_correct ? {} : {CRC});
					read.expect_packet(2'(channel),packets[channel]);
				end
				#50us;
			end
		end
		registers.reset_register(regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME);
		chip_iterator.apply_default();
		#100us;
	endtask
	
	task send_disturbance(int channel, int chiptime, int chips_per_symbol);
		dsi3_slave_tr disturbance;
		dsi3_slave_sequencer_t seq = get_slave_agent(channel).m_sequencer;
		`uvm_do_on_with(disturbance, seq, {
				msg_type == dsi3_pkg::CRM; 
				data.size() == 1;
				chips_per_symbol == local::chips_per_symbol; 
				chiptime == local::chiptime; 
				data[0] inside {4'h1, 4'h5, 4'h6, 4'hA, 4'hB, 4'hF}; // use some symbols without '0' chips
				symbol_coding_error_injection == NEVER_ERROR;})
	endtask
endclass

