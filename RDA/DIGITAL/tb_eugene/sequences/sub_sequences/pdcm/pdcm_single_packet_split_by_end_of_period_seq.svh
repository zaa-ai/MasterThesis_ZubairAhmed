class pdcm_single_packet_split_by_end_of_period_seq extends base_dsi_master_seq;
	
	`uvm_object_utils(pdcm_single_packet_split_by_end_of_period_seq)

	function new(string name = "");
		super.new("pdcm_single_packet_split_by_end_of_period");
	endfunction
	
	task run_tests();
		log_sim_description("single packet is split by end of PDCM period", LOG_LEVEL_SEQUENCE);
		
		get_checker_config().disable_all_master_transmission_checkers();
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			logic[7:0] symbol_count;
			spi_read_pdcm_frame_seq read;
			tdma_scheme_pdcm scheme;
			dsi3_pdcm_packet packet = new();
			if(!packet.randomize() with {data.size() == 18; source_id_symbols == 2'd2;}) `uvm_error(this.get_name(), "randomization error")						
			scheme = tdma_scheme_pdcm_factory::single_pdcm_packet(packet);
			scheme.pdcm_period = 200;
			scheme.packets[0].set_start_time_window(140, 141);
			add_slave_pdcm_scheme(channel, scheme);
			add_slave_pdcm_scheme(channel, tdma_scheme_pdcm_factory::no_answer());
			
			`upload_tdma_scheme_with(scheme, channels == 2'b01 << channel;)
			
			`spi_frame_begin
				`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b01 << channel; pulse_count == 2;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			#500us;
			
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			read.expect_packet_count(2'(channel), 1);
			read.expect_frame_header_flags(2'(channel), {});
			read.expect_flags(2'(channel), 0, {SCE, CRC, TE});
			symbol_count = read.get_symbol_count(2'(channel), 0);
			if(symbol_count < 4 || symbol_count > 6) begin
				`uvm_error(this.get_type_name(), $sformatf("Unexpected symbol count, expected 4-6 symbols, got %0d!", symbol_count))
			end
			
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			read.expect_packet_count(2'(channel), 1);
			read.expect_frame_header_flags(2'(channel), {});
			read.expect_flags(2'(channel), 0, {SCE, CRC, TE}, {SE});
			
			`spi_frame_begin
				`spi_frame_send(read, channel_bits == 2'b01 << channel;)
				`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`spi_frame_end
			read.expect_packet_count(2'(channel), 0);
			read.expect_frame_header_flags(2'(channel), {});
			read.expect_empty(2'(channel), 0);
		end
		get_checker_config().enable_all_master_transmission_checkers();
		#100us;
	endtask
	
endclass
