class p52143_489_seq extends base_dsi_master_seq;

	`uvm_object_utils(p52143_489_seq)
	
	function new(string name = "");
		super.new("p52143_489");
	endfunction

	virtual task run_tests();
		tdma_scheme_pdcm scheme = new();
		get_checker_config().enable_measure_pdcm_pulse = 1'b0;
		
		log_sim_description($sformatf("read and clear data buffer during PDCM reception"), LOG_LEVEL_TOP);
		
		// disable TX shift
		regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.write(status, 16'h0000);
		
		if(!scheme.randomize() with {packets.size() == 1; symbol_count_min == 8; symbol_count_max == 8; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
		scheme.pdcm_period = 300;
		scheme.packets[0].set_start_time_window(20, 40);
		
		`upload_tdma_scheme_with(scheme, channels == 2'b11;)
		
		scheme.packets[0].set_start_time_window(30, 30);
		scheme.packets[0].tolerance_int = 1000;
		for (int channel=0; channel < project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_pdcm(channel, scheme);
		end
		
		clear_all_irqs();
		check_intb(1'b1);
		for(int clear_ns_delay = 0; clear_ns_delay <= 7000; clear_ns_delay += 10) begin
			clear_buffer_during_pdcm(26, clear_ns_delay);
		end
	endtask
	
	task clear_buffer_during_pdcm(int clear_us_delay, int clear_ns_delay);
		
		log_sim_description($sformatf("clear data buffer during PDCM reception, clear command at %0dus + %0dns", clear_us_delay, clear_ns_delay), LOG_LEVEL_OTHERS);
		
		`spi_frame_begin
			`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd5;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		
		// fist pulse
		wait_for_voltage_edge_at_channel(0, 500us);
		#50us;
		// second pulse
		wait_for_voltage_edge_at_channel(0, 500us);
		#50us;
		do_read();
		// third pulse
		wait_for_voltage_edge_at_channel(0, 500us);
		#50us;
		// fourth pulse
		wait_for_voltage_edge_at_channel(0, 500us);
		
		fork
			begin
				#((clear_us_delay * 1us) + (clear_ns_delay * 1ns));
				`spi_frame_begin
					`spi_frame_create(spi_clear_dsi_data_buffers_seq, channel_bits == 2'b11; pdcm_buffer == 1'b1;)
					`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
				`spi_frame_end
				check_intb(1'b1);
				#150us;
				do_read();
			end
		join_none
		#50us;
		// 5th pulse
		wait_for_voltage_edge_at_channel(0, 500us);
		
		#300us;
		do_read();
		#20us
		do_read();
		do_read();
		#100us;
	endtask
	
	task do_read();
		`spi_frame_begin
			`spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
			`uvm_send(frame)
			if(frame.status.get_value(HE) == 1'b1) `uvm_error(this.get_type_name(), "HE flag in status word found")
		end	
	endtask
	
endclass
