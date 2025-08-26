class dsi_shut_off_and_check_pdcm_buffer_seq extends base_dsi_master_seq;

	`uvm_object_utils(dsi_shut_off_and_check_pdcm_buffer_seq) 
    
	function new(string name = "");
		super.new("dsi_shut_off_and_check_pdcm_buffer");
	endfunction
	
	virtual task run_tests();
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b0;
		checker_config::get().disable_all_master_transmission_checkers();
		clear_slave_pdcm_scheme_fifos();
		
		do_shut_off(dsi_enable_shut_off_strategy::create());
		do_shut_off(over_temperature_shut_off_strategy::create());
		do_shut_off(over_voltage_shut_off_strategy::create());
		do_shut_off(under_voltage_shut_off_strategy::create());
		do_shut_off(ldo_shut_off_strategy::create());
		
		checker_config::get().enable_error_if_unknown_transaction_size = 1'b1;
		checker_config::get().enable_all_master_transmission_checkers();
	endtask

	virtual task do_shut_off(shut_off_strategy strategy);
		spi_read_pdcm_frame_seq read1, read2, read3;
		dsi3_pdcm_packet packets[project_pkg::DSI_CHANNELS-1:0][$];
		tdma_scheme_pdcm scheme = tdma_scheme_pdcm_factory::single_packet(8);
		
		log_sim_description($sformatf("switch off channel during PDCM using %s", strategy.get_strategy_name()), LOG_LEVEL_SEQUENCE);
		
		reset();
		#200us;
		
		scheme.pdcm_period = 450;
		scheme.set_source_id_for_all_packets(dsi3_pkg::SID_8Bit);
		scheme.packets[0].earliest_start_time = 280;
		scheme.packets[0].latest_start_time = 300;
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
			repeat(3) begin
				create_pdcm_packets(packets[channel], 2'(1 << channel));
			end
		end
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;
		
		fork
			begin
				`spi_frame_begin
					`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
			end
			begin
				strategy.shut_off_channels(this);
			end
			#500us;	
		join
		
		strategy.enable_channels(this);
		
		`spi_frame_begin
			`spi_frame_send(read1, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read1.expect_flags( 2'(channel), 0, packets[channel][0].crc_correct ? {} : {CRC});
			read1.expect_packet(2'(channel), 0, packets[channel][0]);
		end

		`spi_frame_begin
		`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd1;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#500us;

		`spi_frame_begin
			`spi_frame_send(read2, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read2.expect_flags( 2'(channel), 0, packets[channel][2].crc_correct ? {} : {CRC});
			read2.expect_packet(2'(channel), 0, packets[channel][2]);
		end

		`spi_frame_begin
			`spi_frame_send(read3, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
			
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			read3.expect_empty(2'(channel), 0);
		end
		#100us;
	endtask
	
	function void create_pdcm_packets(ref dsi3_pdcm_packet packets[$], input logic[project_pkg::DSI_CHANNELS-1:0] channels = {project_pkg::DSI_CHANNELS{1'b1}});
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			if(channels[channel] == 1'b1) begin
				dsi3_pdcm_packet pdcm_packets[$];
				dsi3_pdcm_packet packet = create_random_packet(8, dsi3_pkg::SID_8Bit);
				tdma_scheme scheme;
				pdcm_packets.push_back(packet);
				packets.push_back(packet);
				scheme = tdma_scheme_pdcm_factory::multiple_pdcm_packets(pdcm_packets);
				scheme.packets[0].set_start_time_window(290, 290);
				add_slave_pdcm_scheme(channel, scheme);
			end
		end
	endfunction
endclass