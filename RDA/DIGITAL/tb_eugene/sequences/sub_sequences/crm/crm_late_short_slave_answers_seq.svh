class crm_late_short_slave_answers_seq extends base_dsi_master_seq;

	`uvm_object_utils(crm_late_short_slave_answers_seq)
	chip_times_iterator_with_register_model chip_iterator;
	
	function new(string name = "");
		super.new("crm_late_short_slave_answers");
	endfunction : new
	
	virtual task run_tests();
		log_sim_description("late too short slave answers in CRM", LOG_LEVEL_SEQUENCE);
		
		get_checker_config().set_master_transmission_checker_enable(0, 1'b0);
		get_checker_config().set_master_transmission_checker_enable(1, 1'b0);
		
		chip_iterator = new(regmodel);
		while(chip_iterator.has_next()) begin
			int chip_time = chip_iterator.get_current();
			chip_iterator.apply_next();

			log_sim_description($sformatf("late too short slave answers in CRM using %0d us chiptime", chip_time), LOG_LEVEL_OTHERS);
			
			repeat(10) begin
				int start_time = 320 + (8 * 3 * chip_time * 3/4);
				dsi3_packet packets[project_pkg::DSI_CHANNELS-1:0];
				random_slave_scheme(start_time, 1, 7, chip_time, packets);
					
				`spi_frame_begin
					`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				#600us;
				
				for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
					spi_read_crm_data_packets_seq read;
					int symbol_count;
					
					`spi_frame_begin
						`spi_frame_send(read, channel_bits == 2'b01 << channel;)
						`spi_frame_create(spi_tx_crc_request_seq,)
					`spi_frame_end
					
					symbol_count = int'(read.get_symbol_count(2'(channel)));
					
					if(symbol_count >= 4) begin
						logic[31:0] mask = common_env_pkg::create_symbol_mask(symbol_count);
						logic[15:0] word_0 = packets[channel].get_word(0) & mask[31:16];
						
						read.expect_flags(2'(channel), {CRC, SCE, TE});
						read.expect_packet_data(2'(channel), 0, word_0);
						
						if(symbol_count > 4) begin
							logic[15:0] word_1 = packets[channel].get_word(1) & mask[15:0];
							read.expect_packet_data(2'(channel), 1, word_1);
						end
					end
					else begin
						read.expect_empty_data(2'(channel), {SCE});
					end
				end
				#100us;
			end
		end
		chip_iterator.apply_default();
		get_checker_config().enable_all_master_transmission_checkers();
	endtask
endclass